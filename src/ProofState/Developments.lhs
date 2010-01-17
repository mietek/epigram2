\section{Developments}
\label{sec:developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs #-}

> module ProofState.Developments where

> import Data.Foldable
> import Data.List
> import Data.Traversable

> import Kit.BwdFwd

> import NameSupply.NameSupply

> import Evidences.Tm

%endif


\subsection{The |Dev| data-structure}

A |Dev|elopment is a structure containing entries, some of which may
have their own developments, creating a nested tree-like
structure. Developments can be of different nature: hence, their type
is indicated by the |Tip|. Finally, its |NameSupply| for namespace handling
purposes. Initially we had

< type Dev = (Bwd Entry, Tip, NameSupply)

but generalised this to allow other |Traversable| functors |f| in place of |Bwd|, giving

> type Dev f = (f (Entry f), Tip, NameSupply)


\subsubsection{|Tip|}

A |Module| is a development that cannot have a type or value; this may be at the top level
or further in. Developments contained within a female |Entity| may represent |Unknown|s
of a given type, or may be |Defined| as a term with a given type.


> data Tip
>   = Module
>   | Unknown (INTM :=>: TY)
>   | Defined INTM (INTM :=>: TY)
>   deriving Show



\subsubsection{|Entry|}


An |Entry| is either:

\begin{itemize}

\item an |Entity| with its |REF|, the last component of its |Name|
(playing the role of a cache, for performance reasons), and the |INTM|
representation of its type,

\item a module, ie. a |Name| associated with a |Dev| that has no type
or value

\end{itemize}

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


\subsubsection{|Entity|}

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

%if False

> instance Show (Entity Bwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

> instance Show (Entity Fwd) where
>     show (Boy k) = "Boy " ++ show k
>     show (Girl k d) = "Girl " ++ show k ++ " " ++ show d

%endif

We often need to turn the sequence of boys (parameters) under which we
work into the argument spine of a \(\lambda\)-lifted definition.

> boySpine :: Entries -> Spine {TT} REF
> boySpine = foldMap boy where
>   boy :: Entry Bwd -> Spine {TT} REF
>   boy (E r _ (Boy _) _)  = [A (N (P r))]
>   boy _                = []


