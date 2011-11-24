\section{Developments}
\label{sec:ProofState.Structure}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs , StandaloneDeriving #-}

> module ProofState.Structure where

> import Data.List
> import Data.Traversable

> import Kit.BwdFwd

> import Evidences.Tm
> import Evidences.NameSupply

> import Elaboration.ElabProb
> import Elaboration.NewElabMonad

> import DisplayLang.Scheme

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
>                   ,  devHypState      :: HypState
>                   }

We should refactor this so the fields shared with |Layer| are stored
in a single record.

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
>   | SusElab TY (Feeder, NewElab EXP) HKind
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
>   =  EDef     {  edef       :: DEF 
>               ,  dev        :: Dev f
>               ,  scheme     :: Maybe Scheme
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


\subsubsection{Suspension states}

Definitions may have suspended elaboration processes attached,
indicated by a |Suspended| tip. These may be stable or unstable. For
efficiency in the scheduler, each development stores the state of its
least stable child.

> data SuspendState = SuspendUnstable | SuspendStable | SuspendNone
>   deriving (Eq, Show, Enum, Ord)


\subsubsection{|HypState|}

Usually the shared parameters of definitions in the proof state
reflect its hierarchical structure. The contents of a development
share the hypotheses above it (|InheritHyps|). However, sometimes we
need to create a development locally that does not inherit the shared
hypotheses: in this case we use |NixHyps| so there are no hypotheses
in scope.

> data HypState = InheritHyps | NixHyps
>   deriving (Eq, Show, Ord)

> devIsNixed :: Dev f -> Bool
> devIsNixed d = case devHypState d of
>                    NixHyps      -> True
>                    InheritHyps  -> False


\subsection{Looking into an |Entry|}

In the following, we define a bunch of helper functions to access
specific fields of an |Entry|. The field we look for might not exist
for all possible |Entry|, therefore we work in a |Maybe| world. The
naming rule of thumb of these function is: prefix |entry| followed by
the name of one field of the |E| or |M| cases, starting with a capital
letter.

Hence, we have:

> entryDef :: Traversable f => Entry f -> Maybe DEF
> entryDef (EDef d _ _)  = Just d
> entryDef _             = Nothing

> entryName :: Traversable f => Entry f -> Maybe Name
> entryName (EDef d _ _)      = Just $ defName d
> entryName (EModule n _)     = Just n
> entryName (EParam _ _ _ _)  = Nothing


< entryLastName :: Traversable f => Entry f -> (String, Int)
< entryLastName (EEntity _ xn _ _ _)  = xn
< entryLastName (EModule n _)       = last n

> entryScheme :: Traversable f => Entry f -> Maybe Scheme
> entryScheme (EDef _ _ ms)  = ms
> entryScheme _              = Nothing



> entryDev :: Traversable f => Entry f -> Maybe (Dev f)
> entryDev (EDef _ d _)      = Just d
> entryDev (EModule _ d)     = Just d
> entryDev (EParam _ _ _ _)  = Nothing

> modifyEntryDev :: (Traversable f, Traversable g) =>
>                       (Dev f -> Dev g) -> Entry f -> Entry g
> modifyEntryDev f (EDef def dev sch) = EDef def (f dev) sch
> modifyEntryDev f (EModule n dev) = EModule n (f dev)
> modifyEntryDev f (EParam k n t l) = EParam k n t l


> entrySuspendState :: Traversable f => Entry f -> SuspendState
> entrySuspendState e = case entryDev e of
>     Just dev  -> devSuspendState dev
>     Nothing   -> SuspendNone


< entryAnchor :: Traversable f => Entry f -> Maybe String
< entryAnchor (EEntity _ _ _ _ anchor)  = anchor
< entryAnchor (EModule _ _)             = Nothing


\subsection{Entry equality}


Two entries are equal if and only if they have the same name:

< instance Traversable f => Eq (Entry f) where
<     e1 == e2 = entryName e1 == entryName e2



\subsection{Changing the carrier of an |Entry|}


The |entryCoerce| function is quite a thing. When defining |Dev|, we
have been picky in letting any Traversable |f| be the carrier of the
|f (Entry f)|. As shown in
Section~\ref{sec:ProofState.Edition.ProofContext}, we sometimes need
to jump from one Traversable |f| to another Traversable |g|. In this
example, we jump from a |NewsyFwd| -- a |Fwd| list -- to some
|Entries| -- a |Bwd| list.

Changing the type of the carrier is possible for parameters, in which
case we return a |Right entry|. It is not possible for definitions and
modules, in which case we return an unchanged |Left dev|.

> entryCoerce ::  (Traversable f, Traversable g) => 
>                 Entry f -> Either (Dev f) (Entry g)
> entryCoerce (EParam k n t l)  =  Right $ EParam k n t l
> entryCoerce (EDef _ dev _)    =  Left dev
> entryCoerce (EModule _ dev)   =  Left dev



