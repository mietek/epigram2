\section{Navigating in the |ProofState|}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.Navigation where

> import Control.Monad.State
> import Data.Foldable
> import Debug.Trace

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> -- XXX: bug "fix" of the dependency graph:
> import DisplayLang.DisplayTm
> import DisplayLang.Scheme
> import DisplayLang.Name

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.Entries
> import ProofState.Edition.Scope
> import ProofState.Edition.GetSet

> import Evidences.Rules
> import Evidences.Tm

%endif


> getLeaveCurrent :: ProofStateT e (Entry Bwd)
> getLeaveCurrent = do
>     m <- getCurrentEntry
>     Dev above tip root state <- getAboveCursor
>     below <- getBelowCursor
>     let dev = Dev (above <>< below) tip root state
>     case m of
>         CDefinition dkind ref xn ty  ->  return (EDEF ref xn dkind dev ty)
>         CModule n                    ->  return (EModule n dev)


> putLeaveCurrent :: Entry Bwd -> ProofStateT e ()
> putLeaveCurrent (EDEF ref xn dkind dev ty) = do
>     l <- getLayer
>     replaceLayer (l{currentEntry=CDefinition dkind ref xn ty})
>     putAboveCursor dev
> putLeaveCurrent (EModule [] dev) = putAboveCursor dev
> putLeaveCurrent (EModule n dev) = do
>     l <- getLayer
>     replaceLayer (l{currentEntry=CModule n})
>     putAboveCursor dev


