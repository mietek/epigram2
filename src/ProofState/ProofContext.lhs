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

> import Kit.BwdFwd

> import NameSupply.NameSupply

> import ProofState.Developments
> import ProofState.News

> import Evidences.Tm

%endif

Recall from Section~\ref{sec:developments} that

< type Dev = (f (Entry f), Tip, NameSupply)

We ``unzip`` (cf. Huet's Zipper) this type to produce a type representing its
one-hole context, which allows us to keep track of the location of a working
development and perform local navigation easily.
Each |Layer| of the structure is a record with the following fields:
\begin{description}
\item[|elders|] entries appearing above the working development
\item[|mother|] data about the working development
\item[|cadets|] entries appearing below the working development
\item[|laytip|] the |Tip| of the development that contains the mother
\item[|laynsupply|] the |NameSupply| of the development that contains the mother
\end{description}

> data Layer = Layer
>   {  elders    :: Entries
>   ,  mother    :: Mother
>   ,  cadets    :: NewsyEntries
>   ,  laytip    :: Tip
>   ,  laynsupply   :: NameSupply }
>  deriving Show

> data Mother =  GirlMother REF (String, Int) INTM 
>             |  ModuleMother Name
>     deriving Show

> motherName :: Mother -> Name
> motherName (GirlMother (n := _) _ _) = n
> motherName (ModuleMother n) = n

> entryToMother :: Traversable f => Entry f -> Mother
> entryToMother (E ref xn (Girl LETG _) ty) = GirlMother ref xn ty
> entryToMother (M n _) = ModuleMother n

Because we propagate news updates lazily, we may have news bulletins below the
current cursor position, as well as entries. We defined a |newtype| for the
composition of the |Fwd| and |Either NewsBulletin| functors, and use this functor
to contain cadets.

> newtype NewsyFwd x = NF { unNF :: Fwd (Either NewsBulletin x) }

> type NewsyEntries = NewsyFwd (Entry NewsyFwd)


%if False

> instance Show (NewsyFwd (Entry NewsyFwd)) where
>     show (NF ls) = show ls

> instance Show (Entry NewsyFwd) where
>     show (E ref xn e t) = intercalate " " ["E", show ref, show xn, show e, show t]
>     show (M n d) = intercalate " " ["M", show n, show d]

> instance Show (Entity NewsyFwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

> instance Traversable NewsyFwd where
>     traverse g (NF x) = NF <$> traverse (traverse g) x

> instance Foldable NewsyFwd where
>     foldMap = foldMapDefault

> instance Functor NewsyFwd where
>     fmap = fmapDefault

%endif


When moving the cursor, we sometimes need to change the structure that
contains entries, using the following rearrangement functions.

> reverseEntry :: Entry Bwd -> Entry NewsyFwd
> reverseEntry = rearrangeEntry (NF . (fmap Right) . (<>> F0))

> reverseEntry' :: Entry Bwd -> Entry Fwd
> reverseEntry' = rearrangeEntry (<>> F0)

> reverseDev' :: Dev Bwd -> Dev Fwd
> reverseDev' = rearrangeDev (<>> F0)

> rearrangeEntry :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Entry f -> Entry g
> rearrangeEntry h (E ref xn (Boy k) ty)          = E ref xn (Boy k) ty
> rearrangeEntry h (E ref xn (Girl LETG dev) ty)  = E ref xn (Girl LETG (rearrangeDev h dev)) ty
> rearrangeEntry h (M n d)                        = M n (rearrangeDev h d)

> rearrangeEntries :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> f (Entry f) -> g (Entry g)
> rearrangeEntries h xs = h (fmap (rearrangeEntry h) xs)

> rearrangeDev :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Dev f -> Dev g
> rearrangeDev h (xs, tip, nsupply) = (rearrangeEntries h xs, tip, nsupply)


The current proof context is represented by a stack of |Layer|s, along with the
current working development (above the cursor).

> type ProofContext = (Bwd Layer, Dev Bwd)

> emptyContext :: ProofContext
> emptyContext = (B0, (B0, Module, (B0, 0)))


The |greatAuncles| function returns the elder aunts or uncles of the current development,
not including its contents.

> greatAuncles :: ProofContext -> Entries
> greatAuncles (ls, _) = foldMap elders ls

The |auncles| function returns the elder aunts or uncles of the cursor, including the
contents of the current development, thereby giving a list of entries that
are currently in scope.

> auncles :: ProofContext -> Entries
> auncles c@(_, (es, _, _)) = greatAuncles c <+> es

