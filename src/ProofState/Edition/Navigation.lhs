\section{Navigating in the |ProofState|}


%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.Navigation where

> import Kit.BwdFwd

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

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


