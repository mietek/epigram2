\section{Proof Context}
\label{sec:proof_context}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.ProofContext where

> import Control.Applicative
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import NameSupply.NameSupply

> import ProofState.Developments
> import ProofState.News

> import Evidences.Tm

> import DisplayLang.Scheme

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

Recall from Section~\ref{sec:developments} the definition of a
development:

< type Dev = (f (Entry f), Tip, NameSupply)

We ``unzip`` (cf. Huet's Zipper~\cite{huet:zipper}) this type to
produce a type representing its one-hole context. This allows us to
keep track of the location of a working development and perform local
navigation easily.


\subsection{The derivative: |Layer|}


Hence, we define |Layer| by unzipping |Dev|. Each |Layer| of the
zipper is a record with the following fields:

\begin{description}
\item[|elders|] entries appearing above the working development
\item[|mother|] data about the working development
\item[|cadets|] entries appearing below the working development
\item[|laytip|] the |Tip| of the development that contains the mother
\item[|laynsupply|] the |NameSupply| of the development that contains the mother
\end{description}

> data Layer = Layer
>   {  elders       :: Entries
>   ,  mother       :: Mother
>   ,  cadets       :: NewsyEntries
>   ,  laytip       :: Tip
>   ,  laynsupply   :: NameSupply }
>  deriving Show

The derivative makes sense only for |Girl| and |Module|, which have
sub-developments. |Boy| being childless, they ``derive to 0''. Hence,
the data about the working development is the derivative of the |Girl|
and |Module| data-types defined in
Section~\ref{sec:developments_entry}.

> data Mother  = GirlMother REF (String, Int) INTM (Maybe (Scheme INTM))
>              | ModuleMother Name
>     deriving Show

One would expect the |cadets| to be an |Entries|, just as
|elders|. However, the cadets needs to be a richer structure to
support the news infrastructure. Indeed, we propagate reference
updates lazily, by pushing news bulletin below the current cursor.

Hence, the cadets is not only a bunch of entries but it also contains
news. We define a |newtype| for the composition of the |Fwd| and
|Either NewsBulletin| functors, and use this functor to contain
cadets.

> newtype NewsyFwd x = NF { unNF :: Fwd (Either NewsBulletin x) }
>
> type NewsyEntries = NewsyFwd (Entry NewsyFwd)

Note that |elders| are |Entries|, hence a |Bwd| list. The |cadets| are
|NewsyEntries|, hence a |Fwd| list. This justifies some piece of kit
to deal with this global context.


%if False

> instance Show (NewsyFwd (Entry NewsyFwd)) where
>     show (NF ls) = show ls
> instance Show (Entry NewsyFwd) where
>     show (E ref xn e t) = intercalate " " ["E", show ref, show xn, show e, show t]
>     show (M n d) = intercalate " " ["M", show n, show d]
> instance Show (Entity NewsyFwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d _) = "Girl " ++ show k ++ " " ++ show d
> instance Traversable NewsyFwd where
>     traverse g (NF x) = NF <$> traverse (traverse g) x
> instance Foldable NewsyFwd where
>     foldMap = foldMapDefault
> instance Functor NewsyFwd where
>     fmap = fmapDefault

%endif


\subsubsection{Dealing with the local context}

As often, we need some kit. First, getting the name of a |Mother|:

> motherName :: Mother -> Name
> motherName (GirlMother (n := _) _ _ _) = n
> motherName (ModuleMother n) = n

Also, turning an entry (|Girl| or |Module|) into a |Mother|:

> entryToMother :: Traversable f => Entry f -> Mother
> entryToMother (E ref xn (Girl LETG _ ms) ty) = GirlMother ref xn ty ms
> entryToMother (M n _) = ModuleMother n


\subsubsection{Dealing with the global context}


As mentionned above, the global context is dual: on one hand, |elders|
go |Bwd|; on the other hand, |cadets| go |Fwd| with news. Therefore,
when moving the cursor, we sometimes need to change the structure that
contains entries. 

We can change the carrier of |Entry| from |Bwd| to |Fwd| or a
variation thereof:

> reverseEntry :: Entry Bwd -> Entry NewsyFwd
> reverseEntry = rearrangeEntry (NF . (fmap Right) . (<>> F0))
>
> reverseEntry' :: Entry Bwd -> Entry Fwd
> reverseEntry' = rearrangeEntry (<>> F0)

Or we can change the carrier of a whole |Dev| from |Bwd| to |Fwd|:

> reverseDev' :: Dev Bwd -> Dev Fwd
> reverseDev' = rearrangeDev (<>> F0)


> reverseEntries :: Fwd (Entry Bwd) -> NewsyEntries
> reverseEntries es = NF (fmap (Right . reverseEntry) es)

More generally, we can use one of these perverse functions:

> rearrangeEntry :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Entry f -> Entry g
> rearrangeEntry h (E ref xn (Boy k) ty)          = E ref xn (Boy k) ty
> rearrangeEntry h (E ref xn (Girl LETG dev ms) ty)  = E ref xn (Girl LETG (rearrangeDev h dev) ms) ty
> rearrangeEntry h (M n d)                        = M n (rearrangeDev h d)
>
> rearrangeDev :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Dev f -> Dev g
> rearrangeDev h (xs, tip, nsupply) = (rearrangeEntries h xs, tip, nsupply)
>     where  rearrangeEntries ::  (Traversable f, Traversable g) =>
>                                 (forall a. f a -> g a) -> 
>                                 f (Entry f) -> g (Entry g)
>            rearrangeEntries h xs = h (fmap (rearrangeEntry h) xs)



\subsection{The Zipper: |ProofContext|}


Once we have the derivative, the zipper is almost here. Hence, the
current proof context is represented by a stack of |Layer|s, along
with the current working development (above the cursor).

> data ProofContext = PC
>     {  pcLayers :: Bwd Layer
>     ,  pcDev :: Dev Bwd
>     ,  pcCadets :: Fwd (Entry Bwd)
>     }
>   deriving Show
>
> emptyContext :: ProofContext
> emptyContext = PC B0 (B0, Module, (B0, 0)) F0


\subsubsection{Genealogical kit}


The |greatAuncles| function returns the elder aunts or uncles of the
current development, not including its contents.

> greatAuncles :: ProofContext -> Entries
> greatAuncles pc = foldMap elders (pcLayers pc)

The |auncles| function returns the elder aunts or uncles of the
cursor, including the contents of the current development, thereby
giving a list of entries that are currently in scope.

> auncles :: ProofContext -> Entries
> auncles pc@PC{pcDev=(es,_,_)} = greatAuncles pc <+> es

> type BScopeContext = (Bwd (Entries, (String,Int)), Entries) 
> type FScopeContext = ( Fwd (Entry Bwd)
>                      , Fwd ((String, Int), Fwd (Entry Bwd))) 


> inBScope :: ProofContext -> BScopeContext
> inBScope (PC ls (es,_,_) _) = 
>   (fmap (\l -> (elders l,last . motherName . mother $ l)) ls,es)

> inBFScope :: BScopeContext -> FScopeContext
> inBFScope (uess :< (es,u),es') = let (fs, vfss) = inBFScope (uess,es) in 
>   (fs, (u,es' <>> F0) :> vfss)
> inBFScope (B0,es) = (es <>> F0,F0) 


\subsubsection{Gratuitous hackery}

> magicImplName = "impl"

> aunclesToImpl :: ProofContext -> [REF :<: INTM]
> aunclesToImpl pc@PC{pcDev=(es, _, _)} = help (pcLayers pc) (boys es)
>   where
>     help :: Bwd Layer -> [REF :<: INTM] -> [REF :<: INTM]
>     help B0 xs = xs
>     help (ls :< Layer{mother=GirlMother _ (n, _) _ _}) xs
>         | n == magicImplName = xs
>     help (ls :< l) xs = help ls (boys (elders l) ++ xs)

>     boys = foldMap boy

>     boy (E r _ (Boy _) t)  = [r :<: t]
>     boy _                  = []
