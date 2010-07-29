\section{Scope management}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes, StandaloneDeriving #-}

> module ProofState.Edition.Scope where

> import Control.Applicative
> import Data.Foldable
> import Data.List
> import Data.Traversable

> import NameSupply.NameSupply

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofContext

> import Evidences.Tm

> import DisplayLang.Scheme

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif



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
(Section~\ref{subsec:elab-prog-problem}). \pierre{That's all I know
about it, sorry about that.}

\pierre{This really is a hack. I hope it will disapear any time soon.}

> magicImplName = "impl"
>
> definitionsToImpl :: ProofContext -> [REF :<: INTM]
> definitionsToImpl pc@PC{pcAboveCursor=Dev{devEntries=es}} = 
>     help (pcLayers pc) (params es)
>   where
>     help :: Bwd Layer -> [REF :<: INTM] -> [REF :<: INTM]
>     help B0 xs = xs
>     help (ls :< Layer{currentEntry=CDefinition _ _ (n, _) _}) xs
>         | n == magicImplName = xs
>     help (ls :< l) xs = help ls (params (aboveEntries l) ++ xs)
>     params = foldMap param
>     param (EPARAM r _ _ t)  = [r :<: t]
>     param _                 = []
