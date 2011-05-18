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

> {-

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

> -}

> params :: Entries -> [ (Tm {Body, Exp, n}) ]
> params es = fst (params' es [])

> params' :: Entries -> [ (Tm {Body, Exp, n}) ] -> ([ (Tm {Body, Exp, n}) ], Int)
> params' B0 c = (c, 0)
> params' (ez :< (EParam _ s t _)) c = 
>   let  (as, l) = params' ez ((P (l, s, t) :$ B0) : c)
>   in   (as, l+1)
> params' (ez :< _) c = params' ez c


> paramSpine :: Entries -> Bwd (Elim (Tm {Body, Exp, n}))
> paramSpine = fst . paramSpine'

> paramSpine' :: Entries -> (Bwd (Elim (Tm {Body, Exp, n})), Int)
> paramSpine' B0 = (B0, 0)
> paramSpine' (ez :< (EParam _ s t _)) = 
>   let  (az, l) = paramSpine' ez
>   in   (az :< A (P (l, s, t) :$ B0), l+1)
> paramSpine' (ez :< _) = paramSpine' ez


> {-

Similarly, |applySpine| applies a reference to a given spine of
parameters, provided as a spine. These are the shared parameters of a
\(\lambda\)-lifted definition.

> applySpine :: REF -> Entries -> EXTM :=>: VAL
> applySpine ref aus = tm :=>: evTm tm
>   where tm = P ref $:$ paramSpine aus

> -}
