\section{Scope management}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, StandaloneDeriving #-}

> module ProofState.Edition.Scope where

> import Data.Foldable

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext

> import Evidences.Tm
> import Evidences.Eval

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


\subsection{Extracting scopes as entries}


The |globalScope| function returns the parameters and definitions
available in the current development, not including the ones involved
in its construction.

> globalScope :: ProofContext -> Entries
> globalScope pc = foldMap aboveEntries (pcLayers pc)


The |inScope| function returns all parameters and definitions above
the cursor. These are all entries rightfully usable at the cursor's
location.

> inScope :: ProofContext -> Entries
> inScope pc@PC{pcAboveCursor=Dev{devEntries = es}} = globalScope pc <+> es




The |definitionsToImpl| function lists the entries above the cursor
that have been issued during elaboration of a programming problem
(Section~\ref{subsec:Elaborator.Elaborator.elab-prog-problem}). \pierre{That's
all I know about it, sorry about that.}

\pierre{This really is a hack. I hope it will disapear any time soon.}

> magicImplName = "impl"
>
> definitionsToImpl :: ProofContext -> [REF :<: INTM]
> definitionsToImpl pc@PC{pcAboveCursor=Dev{devEntries=es}} = 
>     help (pcLayers pc) (params es)
>   where
>     help :: Bwd Layer -> [REF :<: INTM] -> [REF :<: INTM]
>     help B0 xs = xs
>     help (ls :< Layer{currentEntry=CDefinition _ _ (n, _) _ _}) xs
>         | n == magicImplName = xs
>     help (ls :< l) xs = help ls (params (aboveEntries l) ++ xs)
>     params = foldMap param
>     param (EPARAM r _ _ t _)  = [r :<: t]
>     param _                 = []



\subsection{Manipulating entries as scopes}



We often need to turn the sequence of parameters under which we work
into the argument spine of a \(\lambda\)-lifted definition. Therefore,
let us extract such spine from a list of entries:

> paramREFs :: Entries -> [REF]
> paramREFs = foldMap param where
>   param :: Entry Bwd -> [REF]
>   param  (EPARAM r _ _ _ _)   = [r]
>   param  _                  = []

> paramSpine :: Entries -> Spine {p} REF
> paramSpine = fmap (A . N . P) . paramREFs

Similarly, |applySpine| applies a reference to a given spine of
parameters, provided as a spine. These are the shared parameters of a
\(\lambda\)-lifted definition.

> applySpine :: REF -> Entries -> EXTM :=>: VAL
> applySpine ref aus = tm :=>: evTm tm
>   where tm = P ref $:$ paramSpine aus
