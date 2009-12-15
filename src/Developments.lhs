\section{Developments}
\label{sec:developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators #-}

> module Developments where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Identity
> import Data.Foldable
> import Data.List
> import Data.Maybe
> import Data.Monoid
> import Data.Traversable

> import BwdFwd
> import MissingLibrary
> import Tm
> import Root

%endif

A |Dev| is a structure containing entries, some of which may have their own developments,
creating a nested tree-like structure. It also carries a |Tip| representing the type of
structure, and its |Root| for namespace handling purposes. Initially we had

< type Dev = (Bwd Entry, Tip, Root)

but generalised this to allow other |Traversable| functors |f| in place of |Bwd|, giving

> type Dev f = (f (Entry f), Tip, Root)


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


We can compare entities for equality by comparing their references.

> instance Traversable f => Eq (Entry f) where
>     (E r1 _ _ _) == (E r2 _ _ _)  =  r1 == r2
>     _ == _ = error "instance Eq Entry: cannot compare modules for equality"

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
> data BoyKind   = LAMB | PIB  deriving (Show, Eq)
> data GirlKind  = LETG        deriving (Show, Eq)

> instance Show (Entity Bwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

> instance Show (Entity Fwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

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

> addNews :: NewsBulletin -> (REF, News) -> NewsBulletin
> addNews news (_,    NoNews)    = news
> addNews news (ref,  GoodNews)  = (ref, GoodNews):news

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

The |mergeNews| function takes older and newer bulletins, and composes them to
produce a single bulletin with the worst news about every reference mentioned
in either.

> mergeNews :: NewsBulletin -> NewsBulletin -> NewsBulletin
> mergeNews old [] = old
> mergeNews [] new = new
> mergeNews ((r, n):old) new = mergeNews old ((r, min n (lookupNews new r)):new)


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
>     h (ys :< E y _ (Girl _ _) _)  x i = h ys x i

The |parBind| function $\lambda$-binds over a list $\Delta$ of entries and
$\lambda$- and $\Pi$-binds over a list $\nabla$.

> parBind ::  {- $\Delta$ :: -} Bwd (Entry Bwd) {- $\Gamma$ -} -> 
>             {- $\nabla$ :: -} Bwd (Entry Bwd) {- $\Gamma, \Delta$ -} -> 
>             INTM {- $\Gamma, \Delta, \nabla$ -} ->
>             INTM {- $\Gamma$ -}
> parBind delta nabla t = help delnab nabla (delnab -| t) where
>     delnab = delta <+> nabla
>     help B0                                        B0            t = t
>     help (delta   :< E _ _       (Girl _ _) _)     B0            t = help delta B0 t
>     help (delta   :< E _ (x, _)  (Boy _) _)        B0            t = help delta B0 (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Girl _ _) _)     (nabla :< _)  t = help delnab nabla t
>     help (delnab  :< E _ (x, _)  (Boy LAMB) _)     (nabla :< _)  t = 
>         help delnab nabla (L (x :. t))
>     help (delnab  :< E _ (x, _)  (Boy PIB) s)  (nabla :< _)  t = 
>         help delnab nabla (PI (delnab -| s) (L (x :. t)))


The |liftType| function $\Pi$-binds a type over a list of entries.

> liftType :: Bwd (Entry Bwd) -> INTM -> INTM
> liftType B0 t = t
> liftType (es :< E _ _      (Girl _ _)  _)  t = liftType es t
> liftType (es :< E _ (x,_)  (Boy _)     s)  t = liftType es (PI s (L (x :. t)))


The |inferGoalType| function $\Pi$-binds the type when it encounters a $\lambda$-boy
in the list of entries, and produces |SET| when it encounters a $\Pi$-boy.

> inferGoalType :: Bwd (Entry Bwd) -> INTM -> INTM
> inferGoalType B0 t = t
> inferGoalType (es :< E _ _      (Girl _ _)  _)  t = inferGoalType es t
> inferGoalType (es :< E _ (x,_)  (Boy LAMB)  s)  t = inferGoalType es (PI s (L (x :. t)))
> inferGoalType (es :< E _ (x,_)  (Boy PIB)   s)  t = inferGoalType es SET


\subsection{Traversal}

A |Dev| is not truly |Traversable|, but it supports |traverse|-like operations that update
its references:

> traverseDev :: (Applicative f, Traversable g) => (REF -> f REF) -> (Dev g) -> f (Dev g)
> traverseDev f (es, t, r) = 
>   (|(\x y z -> (x,y,z)) (traverse (traverseEntry f) es) (traverseTip f t) ~r|)

> traverseTip :: Applicative f => (REF -> f REF) -> Tip -> f Tip
> traverseTip f Module                   = pure Module
> traverseTip f (Unknown (t :=>: v))     = (|Unknown (|traverse f t :=>: traverseVal f v|)|)
> traverseTip f (Defined tm (t :=>: v))  =
>   (|Defined (traverse f tm) (|traverse f t :=>: traverseVal f v|)|)

> traverseEntry :: (Applicative f, Traversable g) => (REF -> f REF) -> (Entry g) -> f (Entry g)
> traverseEntry f (E r (x,i) e t) = (|E (f r) (pure (x,i)) (traverseEntity f e) (traverse f t)|)

> traverseEntity :: (Applicative f, Traversable g) => (REF -> f REF) -> (Entity g) -> f (Entity g)
> traverseEntity f (Boy bk)     = (|Boy (traverseBK f bk)|)
> traverseEntity f (Girl gk dv) = (|Girl (traverseGK f gk) (traverseDev f dv)|)

> traverseBK :: Applicative f => (REF -> f REF) -> BoyKind -> f BoyKind
> traverseBK f LAMB = pure LAMB
> traverseBK f PIB =  pure PIB

> traverseGK :: Applicative f => (REF -> f REF) -> GirlKind -> f GirlKind
> traverseGK f LETG = pure LETG
