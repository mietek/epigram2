\section{Proof Context}
\label{sec:ProofState.ProofContext}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, StandaloneDeriving,
>              GeneralizedNewtypeDeriving #-}

> module ProofState.ProofContext where

> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Error
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.News
> import Evidences.ErrorHandling

> import ProofState.Structure

> import DisplayLang.Scheme

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

Recall from Section~\ref{sec:ProofState.Structure} the
definition of a development:

< type Dev = (f (Entry f), Tip, NameSupply)

We ``unzip`` (cf. Huet's Zipper~\cite{huet:zipper}) this type to
produce a type representing its one-hole context. This allows us to
keep track of the location of a working development and perform local
navigation easily.


\subsection{The derivative: |Layer|}


Hence, we define |Layer| by unzipping |Dev|. Each |Layer| of the
zipper is a record with the following fields:

\begin{description}
\item[|aboveEntries|] appearing \emph{above} the working development
\item[|currenEntry|] data about the working development
\item[|belowEntries|] appearing \emph{below} the working development
\item[|layTip|] the |Tip| of the development that contains the current entry
\item[|layNSupply|] the |NameSupply| of the development that contains the 
                    current entry
\item[|laySuspendState|] the state of the development that contains the
                         current entry
\end{description}

> data Layer = Layer
>   {  aboveEntries     :: Entries
>   ,  currentEntry     :: CurrentEntry
>   ,  belowEntries     :: NewsyEntries
>   ,  layTip           :: Tip
>   ,  layNSupply       :: NameSupply
>   ,  layLevelCount    :: Int
>   ,  laySuspendState  :: SuspendState
>   ,  layHypState      :: HypState
>   }
>  deriving Show

The derivative makes sense only for definitions and modules, which
have sub-developments. Parameters being childless, they `derive to
0'. Hence, the data about the working development is the derivative of
the Definition and Module data-types defined in
Section~\ref{subsubsec:ProofState.Structure.entry}.

> data CurrentEntry  =  CDefinition DEF (Maybe Scheme)
>                    |  CModule Name
>     deriving Show

One would expect the |belowEntries| to be an |Entries|, just as the
|aboveEntries|. However, the |belowEntries| needs to be a richer
structure to support the news infrastructure
(Section~\ref{sec:Evidences.News}). Indeed, we propagate
reference updates lazily, by pushing news bulletin below the current
cursor.

Hence, the |belowEntries| are not only normal entries but also contain
news. We define a |newtype| for the composition of the |Fwd| and
|Either NewsBulletin| functors, and use this functor for defining the
type of |belowEntries|.

> newtype NewsyFwd x = NF { unNF :: Fwd (Either NewsBulletin x) }
>
> type NewsyEntries = NewsyFwd (Entry NewsyFwd)

Note that |aboveEntries| are |Entries|, that is |Bwd|
list. |belowEntries| are |NewsyEntries|, hence |Fwd| list. This
justifies some piece of kit to deal with this global context.


%if False

> deriving instance Show (Dev NewsyFwd)

> instance Show (NewsyFwd (Entry NewsyFwd)) where
>     show (NF ls) = show ls
> instance Show (Entry NewsyFwd) where
>     show (EDef def dev sch) = intercalate " " ["D", show def, show dev, show sch]
>     show (EParam k n t l) = intercalate " " ["P", show k, show n, show t, show l]
>     show (EModule n dev) = intercalate " " ["M", show n, show dev]

> instance Traversable NewsyFwd where
>     traverse g (NF x) = NF <$> traverse (traverse g) x

< instance Foldable NewsyFwd where
<     foldMap = foldMapDefault
< instance Functor NewsyFwd where
<     fmap = fmapDefault

%endif

\subsection{The Zipper: |ProofContext|}


Once we have the derivative, the zipper is almost here. The proof
context is represented by a stack of layers (|pcLayers|), ending with
the working development (|pcDev|) above the cursor and the entries
below the cursor (|pcBelowCursor|)..

> data ProofContext = PC
>     {  pcLayers       :: Bwd Layer
>     ,  pcAboveCursor  :: Dev Bwd
>     ,  pcBelowCursor  :: Fwd (Entry Bwd)
>     }
>   deriving Show

The |emptyContext| corresponds to the following (purposedly verbose)
definition:

> emptyContext :: ProofContext
> emptyContext = PC  {  pcLayers = B0
>                    ,  pcAboveCursor = Dev  {  devEntries       = B0
>                                            ,  devTip           = Module
>                                            ,  devNSupply       = (B0, 0)
>                                            ,  devSuspendState  = SuspendNone
>                                            ,  devLevelCount    = 0
>                                            ,  devHypState      = InheritHyps
>                                            }
>                    ,  pcBelowCursor = F0 }



\subsubsection{Manipulating the |CurrentEntry|}

As with entries in Section~\ref{sec:ProofState.Structure}, we
need some kit operating on any kind of |CurrentEntry|. So far, this is
restricted to getting its name:

> currentEntryName :: CurrentEntry -> Name
> currentEntryName  (CDefinition d _)  = defName d
> currentEntryName  (CModule n)      = n


There is an obvious (forgetful) map from entry (Definition or Module)
to a current entry:

> mkCurrentEntry :: Traversable f => Entry f -> CurrentEntry
> mkCurrentEntry (EDef def _ sch)  = CDefinition def sch
> mkCurrentEntry (EModule n _)     = CModule n




\subsubsection{From Above to Below, and back}


The |aboveEntries| and |belowEntries| give a certain twist to the
visit of a |Layer|: on one hand, |aboveEntries| go |Bwd|; on the other
hand, |belowEntries| go |Fwd| with news. Therefore, when moving the
cursor, we sometimes need to change the structure that contains
entries.

We define such `rearranging' function by mutual induction on |Entry f|
and |Dev f|:

> rearrangeEntry ::  (Traversable f, Traversable g) =>
>                    (forall a. f a -> g a) -> Entry f -> Entry g
> rearrangeEntry h (EParam k n t l)    =  EParam k n t l
> rearrangeEntry h (EDef def dev sch)  =  EDef def (rearrangeDev h dev) sch
> rearrangeEntry h (EModule n d)       =  EModule n (rearrangeDev h d)
>
> rearrangeDev :: (Traversable f, Traversable g) =>
>     (forall a. f a -> g a) -> Dev f -> Dev g
> rearrangeDev h d@(Dev {devEntries=xs}) = d{devEntries=rearrangeEntries h xs}
>     where  rearrangeEntries ::  (Traversable f, Traversable g) =>
>                                 (forall a. f a -> g a) -> 
>                                 f (Entry f) -> g (Entry g)
>            rearrangeEntries h xs = h (fmap (rearrangeEntry h) xs)


Hence, we can change the carrier of |Entry| from |Bwd| to |Fwd| or a
variation thereof:

> reverseEntry :: Entry Bwd -> Entry NewsyFwd
> reverseEntry = rearrangeEntry (NF . (fmap Right) . (<>> F0))
>
> reverseEntries :: Fwd (Entry Bwd) -> NewsyEntries
> reverseEntries es = NF $ fmap (Right . reverseEntry) es

Or we can change the carrier of a whole |Dev| from |Bwd| to |Fwd|:

> reverseDev :: Dev Bwd -> Dev Fwd
> reverseDev = rearrangeDev (<>> F0)




\subsection{Defining the Proof State monad}


The proof state monad provides access to the |ProofContext| as in a
|State| monad, but with the possibility of command failure represented
by |Either StackError|. 

> newtype ProofState a = ProofState
>     {unProofState :: StateT ProofContext (Either StackError) a}
>   deriving  ({-Applicative
>             ,-}Alternative
>             ,{-Functor
>             ,-}MonadError StackError
>             ,  MonadPlus
>             ,  MonadState ProofContext
>             )

This is annoying. We need |ProofState| to be a newtype so that we can
override the |fail| behaviour of the |Monad| instance to invoke
|throwError| rather than crashing with |error|.

> instance Monad ProofState where
>     return              = ProofState . return
>     ProofState x >>= f  = ProofState (x >>= (unProofState . f))
>     fail s              = throwError [err s]


> evalProofState :: ProofState a -> ProofContext -> Either StackError a
> evalProofState  = evalStateT . unProofState

> runProofState :: ProofState a -> ProofContext -> Either StackError (a, ProofContext)
> runProofState   = runStateT . unProofState

> execProofState :: ProofState a -> ProofContext -> Either StackError ProofContext
> execProofState  = execStateT . unProofState





\subsection{Extracting scopes as entries}


The |globalScope| function returns the parameters and definitions
available in the current development, not including the ones involved
in its construction.

> globalScope :: ProofContext -> Entries
> globalScope pc = help (pcLayers pc)
>   where
>     help :: Bwd Layer -> Entries
>     help B0 = B0
>     help (ls :< l@(Layer{layHypState = NixHyps}))  = defsInScope ls <+> aboveEntries l
>     help (ls :< l)                                 = help ls <+> aboveEntries l

>     defsInScope :: Bwd Layer -> Entries
>     defsInScope B0 = B0
>     defsInScope (ls :< l) = defsInScope ls <+> filterOutParams (aboveEntries l)

> filterOutParams :: Entries -> Entries
> filterOutParams = bwdFilter (not . isParam)
>   where
>     isParam (EParam _ _ _ _)  = True
>     isParam _                 = False


The |inScope| function returns all parameters and definitions above
the cursor. These are all entries rightfully usable at the cursor's
location.

> inScope :: ProofContext -> Entries
> inScope (PC{pcAboveCursor=Dev{devEntries = es, devHypState = NixHyps}}) = es
> inScope pc@PC{pcAboveCursor=Dev{devEntries = es}} = globalScope pc <+> es




The |definitionsToImpl| function lists the entries above the cursor
that have been issued during elaboration of a programming problem
(Section~\ref{subsec:Elaborator.Elaborator.elab-prog-problem}). \pierre{That's
all I know about it, sorry about that.}

\pierre{This really is a hack. I hope it will disapear any time soon.}


> magicImplName = "impl"
>
> definitionsToImpl :: ProofContext -> [(Int, String, TY)]
> definitionsToImpl pc@PC{pcAboveCursor=Dev{devEntries=es}} = 
>     help (pcLayers pc) (params es)
>   where
>     help :: Bwd Layer -> [(Int, String, TY)] -> [(Int, String, TY)]
>     help B0 xs = xs
>     help (ls :< Layer{currentEntry=CDefinition d _}) xs
>         | (fst . last . defName $ d) == magicImplName = xs
>     help (ls :< l) xs = help ls (params (aboveEntries l) ++ xs)
>     params = foldMap param
>     param (EParam _ s t l)  = [(l,s,t)]
>     param _                 = []




\subsection{Manipulating entries as scopes}



We often need to turn the sequence of parameters under which we work
into the argument spine of a \(\lambda\)-lifted definition. Therefore,
let us extract such spine from a list of entries:

> params :: Entries -> [ (Tm {Body, Exp, n}) ]
> params es = herp es []
>   where herp :: Entries -> [ (Tm {Body, Exp, n}) ] -> [ (Tm {Body, Exp, n}) ]
>         herp B0 c = c
>         herp (ez :< (EParam _ s t l)) c = herp ez ((P (l, s, t) :$ B0) : c)
>         herp (ez :< _) c = herp ez c


> paramSpine :: Entries -> Bwd (Elim (Tm {Body, Exp, n}))
> paramSpine B0 = B0
> paramSpine (ez :< (EParam _ s t l)) = paramSpine ez :< A (P (l, s, t) :$ B0)
> paramSpine (ez :< _) = paramSpine ez

> paramsBwd :: Entries -> Bwd (Int, String, TY)
> paramsBwd B0 = B0
> paramsBwd (ez :< (EParam _ s t l)) = paramsBwd ez :<  (l, s, t) 
> paramsBwd (ez :< _) = paramsBwd ez

> params' :: Entries -> [ (Int, String, TY) ]
> params' es = herp es []
>   where herp :: Entries -> [ (Int, String, TY) ] -> [ (Int, String, TY) ]
>         herp B0 c = c
>         herp (ez :< (EParam _ s t l)) c = herp ez ((l, s, t) : c)
>         herp (ez :< _) c = herp ez c



Similarly, |applySpine| applies a reference to a given spine of
parameters, provided as a spine. These are the shared parameters of a
\(\lambda\)-lifted definition.

> applySpine :: EXP -> Entries -> EXP
> applySpine ref aus = ref $$$ paramSpine aus

