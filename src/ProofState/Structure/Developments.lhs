\section{Developments}
\label{sec:ProofState.Structure.Developments}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs , StandaloneDeriving #-}

> module ProofState.Structure.Developments where

> import Data.List
> import Data.Traversable

> import Kit.BwdFwd

> import Evidences.Tm
> import Evidences.NameSupply

> import Elaboration.ElabProb

> -- import DisplayLang.Scheme

%endif


\subsection{The |Dev| data-structure}


A |Dev|elopment is a structure containing entries, some of which may
have their own developments, creating a nested tree-like
structure. Developments can be of different nature: this is indicated
by the |Tip|. A development also keeps a |NameSupply| at hand, for
namespace handling purposes. Initially we had the following
definition:

< type Dev = (Bwd Entry, Tip, NameSupply)

but generalised this to allow other |Traversable| functors |f| in
place of |Bwd|, and to store a |SuspendState|, giving:

> data Dev f = Dev  {  devEntries       :: f (Entry f)
>                   ,  devTip           :: Tip
>                   ,  devNSupply       :: NameSupply
>                   ,  devLevelCount    :: Int
>                   ,  devSuspendState  :: SuspendState
>                   }

%if False

> deriving instance Show (Dev Fwd)
> deriving instance Show (Dev Bwd)

> deriving instance Show (Entry Fwd)
> deriving instance Show (Entry Bwd)

%endif


\subsubsection{|Tip|}

There are two kinds of Developments available: modules and definitions.
A |Module| is a development that cannot have a type or value, but
simply packs up some other developments. A development holding a
definition can be in one of three states: an |Unknown| of the given
type, a |Suspended| elaboration problem for producing a value of the
type (see section~\ref{sec:Elaboration.ElabMonad}), or a |Defined| term
of the type. Note that the type is presented as both a term and a
value for performance purposes. 

> data HKind = Crying String | Waiting | Hoping
>   deriving Show

> data Tip
>   = Module
>   | Unknown TY HKind
>   | Suspended TY EProb HKind
>   | Defined (TY :>: EXP)
>   deriving Show


\subsubsection{|Entry|}
\label{subsubsec:ProofState.Structure.Developments.entry}

As mentionned above, a |Dev| is a kind of tree. The branches are
introduced by the container |f (Entry f)| where |f| is Traversable,
typically a backward list. 

An |Entry| leaves a choice of shape for the branches. Indeed, it can
either be:

\begin{itemize}

\item an |Entity| with a |REF|, the last component of its |Name|
(playing the role of a cache, for performance reasons), and the term
representation of its type, or

\item a module, ie. a |Name| associated with a |Dev| that has no type
or value

\end{itemize}

> data Traversable f => Entry f
>   =  EDef     {  def        :: DEF 
>               ,  dev        :: Dev f
>               }
>   |  EParam   {  paramKind   :: ParamKind
>               ,  paramName   :: String
>               ,  paramType   :: TY
>               ,  paramLevel  :: Int
>               }
>   |  EModule  {  name       :: Name
>               ,  dev        :: (Dev f)
>               }

In the Module case, we have already tied the knot, by defining |M|
with a sub-development. In the Entity case, we give yet another choice
of shape, thanks to the |Entity f| constructor. This constructor is
defined in the next section.

Typically, we work with developments that use backwards lists, hence
|f| is |Bwd|:

> type Entries = Bwd (Entry Bwd)


%if False

> {-
> instance Show (Entry Bwd) where
>     show (EEntity ref xn e t a) = intercalate " " ["E", show ref, show xn, show e, show t, show a]
>     show (EModule n d) = intercalate " " ["M", show n, show d]
> instance Show (Entry Fwd) where
>     show (EEntity ref xn e t a) = intercalate " " ["E", show ref, show xn, show e, show t, show a]
>     show (EModule n d) = intercalate " " ["M", show n, show d]
> -}

%endif

\begin{danger}[Name caching]

We have mentionned above that an Entity |E| caches the last component
of its |Name| in the |(String, Int)| field. Indeed, grabing that
information asks for traversing the whole |Name| up to the last
element:

> mkLastName :: DEF -> (String, Int)
> mkLastName = last . defName

As we will need it quite frequently for display purposes, we extract
it once and for all with |lastName| and later rely on the cached version.

\end{danger}


\paragraph{Kinds of Definitions:}

A \emph{definition} eventually constructs a term, by a (possibly
empty) development of sub-objects. The |Tip| of this sub-development
will be |Unknown|, |Suspended| or |Defined|.

A programming problem is a special kind of definition: it follows a
type |Scheme| (Section~\ref{sec:DisplayLang.Scheme}), the high-level
type of the function we are implementing.

> {-
> data DefKind = LETG |  PROG (Scheme INTM)

%if False

> instance Show DefKind where
>     show LETG      = "LETG"
>     show (PROG _)  = "PROG"

%endif

> -}



%if False

> {-
> instance Show (Entity Bwd) where
>     show (Parameter k) = "Param " ++ show k
>     show (Definition k d) = "Def " ++ show k ++ " " ++ show d

> instance Show (Entity Fwd) where
>     show (Parameter k) = "Param " ++ show k
>     show (Definition k d) = "Def " ++ show k ++ " " ++ show d 
> -}

%endif

\subsubsection{Suspension states}

Definitions may have suspended elaboration processes attached,
indicated by a |Suspended| tip. These may be stable or unstable. For
efficiency in the scheduler, each development stores the state of its
least stable child.

> data SuspendState = SuspendUnstable | SuspendStable | SuspendNone
>   deriving (Eq, Show, Enum, Ord)

