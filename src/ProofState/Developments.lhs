\section{Developments}
\label{sec:developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Developments where

> import Control.Applicative
> import Control.Monad.Identity
> import Data.Foldable
> import Data.List
> import Data.Maybe
> import Data.Monoid hiding (All)
> import Data.Traversable

> import Kit.BwdFwd

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Mangler

%endif

A |Dev| is a structure containing entries, some of which may have their own developments,
creating a nested tree-like structure. It also carries a |Tip| representing the type of
structure, and its |NameSupply| for namespace handling purposes. Initially we had

< type Dev = (Bwd Entry, Tip, NameSupply)

but generalised this to allow other |Traversable| functors |f| in place of |Bwd|, giving

> type Dev f = (f (Entry f), Tip, NameSupply)


A |Module| is a development that cannot have a type or value; this may be at the top level
or further in. Developments contained within a female |Entity| may represent |Unknown|s
of a given type, or may be |Defined| as a term with a given type.

> data Tip
>   = Module
>   | Unknown (INTM :=>: TY)
>   | Defined INTM (INTM :=>: TY)
>   deriving Show


An |Entry| is either an |Entity| with its |REF|, the last component of its |Name|
and the |INTM| representation of its type, or it is a module (a |Name| associated
with a |Dev| that has no type or value).

> data Traversable f => Entry f
>   =  E REF (String, Int) (Entity f) INTM
>   |  M Name (Dev f)


> entryDev :: Traversable f => Entry f -> Dev f
> entryDev (E _ _ (Boy _) _) = error "entryDev: boys have no development"
> entryDev (E _ _ (Girl LETG d) _) = d
> entryDev (M _ d) = d

> entryHasDev :: Traversable f => Entry f -> Bool
> entryHasDev (E _ _ (Boy _)     _)  = False
> entryHasDev (E _ _ (Girl _ _)  _)  = True
> entryHasDev (M _ _)                = True

> entryLastName :: Traversable f => Entry f -> (String, Int)
> entryLastName (E _ xn _ _) = xn
> entryLastName (M n _) = last n

> entryName :: Traversable f => Entry f -> Name
> entryName (E (n := _) _ _ _) = n
> entryName (M n _) = n

> replaceEntryDev :: (Traversable f, Traversable g) => Entry f -> Dev g -> Entry g
> replaceEntryDev (E _ _ (Boy _) _) _ = error "replaceEntryDev: boys have no development"
> replaceEntryDev e@(E ref xn (Girl LETG _) ty) dev = E ref xn (Girl LETG dev) ty
> replaceEntryDev (M n _) dev = M n dev

The |coerceEntry| function attempts to change the type of the |Dev| functor in an
entry, yielding |Right entry| if this is possible (for boys) or |Left dev| if
not (for girls and modules).  

> coerceEntry :: (Traversable f, Traversable g) => Entry f -> Either (Dev f) (Entry g)
> coerceEntry (E ref  xn  (Boy k)          ty)  = Right (E ref xn (Boy k) ty)
> coerceEntry (E _    _   (Girl LETG dev)  _)   = Left dev
> coerceEntry (M _ dev)                         = Left dev

We can compare entities for equality by comparing their names.

> instance Traversable f => Eq (Entry f) where
>     e1 == e2 = entryName e1 == entryName e2


Typically, we want to work with developments that use backwards lists, so define

> type Entries = Bwd (Entry Bwd)

%if False

> instance Show (Entry Bwd) where
>     show (E ref xn e t) = intercalate " " ["E", show ref, show xn, show e, show t]
>     show (M n d) = intercalate " " ["M", show n, show d]

> instance Show (Entry Fwd) where
>     show (E ref xn e t) = intercalate " " ["E", show ref, show xn, show e, show t]
>     show (M n d) = intercalate " " ["M", show n, show d]

%endif


The last component of the name is cached because we will need it quite frequently for
display purposes. We can easily (but inefficiently) extract it from a reference:

> lastName :: REF -> (String, Int)
> lastName (n := _) = last n


An |Entity| may be a |Boy| (which does not have children) or a |Girl| (which may do).
A |Girl| is a definition, with a (possibly empty) development of sub-objects, which
has a |Tip| that is |Unknown| or |Defined|.
A |Boy| represents a parameter (either a $\lambda$ or $\Pi$ abstraction), which scopes
over all following entries and the definition (if any) in its development.

> data Traversable f => Entity f
>   =  Boy   BoyKind
>   |  Girl  GirlKind (Dev f)
>
> data BoyKind   = LAMB | ALAB | PIB  deriving (Show, Eq)
> data GirlKind  = LETG        deriving (Show, Eq)

> instance Show (Entity Bwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

> instance Show (Entity Fwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

We often need to turn the sequence of boys (parameters) under which we
work into the argument spine of a \(\lambda\)-lifted definition.

> boySpine :: Entries -> Spine {TT} REF
> boySpine = foldMap boy where
>   boy :: Entry Bwd -> Spine {TT} REF
>   boy (E r _ (Boy _) _)  = [A (N (P r))]
>   boy _                = []


\subsection{News about updated references}

|News| represents possible changes to references. At the moment, it may be |GoodNews|
(the reference has become more defined) or |NoNews| (even better from our perspective,
as the reference has not changed). Note that |News| is ordered by increasing ``niceness''.

When we come to implement functionality to remove definitions from the proof state,
we will also need |BadNews| (the reference has changed but is not more informative)
and |DeletedNews| (the reference has gone completely).

> data News = DeletedNews | BadNews | GoodNews | NoNews deriving (Eq, Ord, Show)

> instance Monoid News where
>     mempty   = NoNews
>     mappend  = min

A |NewsBulletin| is a list of pairs of updated references and the news about them.

> type NewsBulletin = [(REF, News)]

The |addNews| function adds the given news to the bulletin, if it is newsworthy.
Conor made it delete old versions but minimize news goodness.

> addNews :: (REF, News) -> NewsBulletin ->  NewsBulletin
> addNews (_,  NoNews)  old  = old
> addNews (r,  n)       old  = (r, min n n') : old' where
>   (n', old') = seek old
>   seek [] = (NoNews, [])
>   seek ((r', n') : old) | r == r' = (n', old)
>   seek (rn : old) = (n', rn : old') where (n', old') = seek old

The |lookupNews| function returns the news about a reference contained in the
bulletin, which may be |NoNews| if the reference is not present.

> lookupNews :: NewsBulletin -> REF -> News
> lookupNews nb ref = fromMaybe NoNews (lookup ref nb)

The |getLatest| function returns the most up-to-date copy of the given reference,
either the one from the bulletin if it is present, or the one passed in otherwise.
The slightly odd recursive case arises because equality for references just compares
their names.

> getLatest :: NewsBulletin -> REF -> REF
> getLatest []                ref = ref
> getLatest ((ref', _):news)  ref
>     | ref == ref'  = ref'
>     | otherwise    = getLatest news ref

\conor{Need to modify this to update FAKEs correctly.}

The |mergeNews| function takes older and newer bulletins, and composes them to
produce a single bulletin with the worst news about every reference mentioned
in either.

> mergeNews :: NewsBulletin -> NewsBulletin -> NewsBulletin
> mergeNews new [] = new
> mergeNews new old = Data.List.foldr addNews old new


\subsection{Lambda-lifting and discharging}

The |(-||)| operator takes a list of entries and a term, and changes the term
so that boys in the list of entries are represented by de Brujin indices.

> (-|) :: Bwd (Entry Bwd) -> INTM -> INTM
> es -| t = disMangle es 0 %% t
>   where
>     disMangle :: Bwd (Entry Bwd) -> Int -> Mangle Identity REF REF
>     disMangle ys i = Mang
>       {  mangP = \ x ies -> (|(h ys x i $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> disMangle ys (i + 1)
>       }
>     h B0                        x i  = P x
>     h (ys :< E y _ (Boy _) _)     x i
>       | x == y     = V i
>       | otherwise  = h ys x (i + 1)
>     h (ys :< E _ _ (Girl _ _) _)  x i = h ys x i
>     h (ys :< M _ _) x i = h ys x i

The |parBind| function $\lambda$-binds over a list $\Delta$ of entries and
$\lambda$- and $\Pi$-binds over a list $\nabla$.

> parBind ::  {- $\Delta$ :: -} Bwd (Entry Bwd) {- $\Gamma$ -} -> 
>             {- $\nabla$ :: -} Bwd (Entry Bwd) {- $\Gamma, \Delta$ -} -> 
>             INTM {- $\Gamma, \Delta, \nabla$ -} ->
>             INTM {- $\Gamma$ -}
> parBind delta nabla t = help delnab nabla (delnab -| t) where
>     delnab = delta <+> nabla
>     help B0                                     B0            t = t
>     help (delta   :< E _ (x, _)  (Boy _) _)     B0            t = help delta B0 (L (x :. t))
>     help (delta   :< _)                         B0            t = help delta B0 t
>     help (delnab  :< E _ (x, _)  (Boy LAMB) _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy ALAB) _)  (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy PIB) s)   (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))
>     help (delnab  :< _)                         (nabla :< _)  t = help delnab nabla t



The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Bwd (Entry Bwd) -> INTM -> INTM
> liftType es t = pis es (es -| t) where
>   pis B0 t = t
>   pis (es :< E _ (x,_)  (Boy _)     s)  t = pis es (PI (es -| s) (L (x :. t)))
>   pis (es :< _)                         t = pis es t

The |inferGoalType| function $\Pi$-binds the type when it encounters a $\lambda$-boy
in the list of entries, and produces |SET| when it encounters a $\Pi$-boy.

> inferGoalType :: Bwd (Entry Bwd) -> INTM -> INTM
> inferGoalType B0 t = t
> inferGoalType (es :< E _ (x,_)  (Boy LAMB)  s)  t        = inferGoalType es (PI (es -| s) (L (x :. t)))
> inferGoalType (es :< E _ (x,_)  (Boy ALAB)  s)  (PRF t)  = inferGoalType es (PRF (ALL (es -| s) (L (x :. t))))
> inferGoalType (es :< E _ (x,_)  (Boy PIB)   s)  SET      = inferGoalType es SET
> inferGoalType (es :< _)                         t        = inferGoalType es t

