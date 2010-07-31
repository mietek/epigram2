\section{Fake references}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Edition.FakeRef where

> import Control.Monad.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofContext
> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Evidences.Tm
> import Evidences.Rules

%endif


The |getFakeMother| command returns a neutral application of a fake reference
that represents the mother of the current location. Note that its type is
$\lambda$-lifted over its great uncles, but it is then applied to them (as
shared parameters).

\pierre{This requires further documentation. I'm not familiar with
these fake things, so I cannot tell more about it now.}

> getFakeRef :: ProofState REF
> getFakeRef = do
>    CDefinition _  (cEntryName := HOLE _ :<: ty) _ _ <- getCurrentEntry
>    return $ cEntryName := FAKE :<: ty

> getFakeMother :: ProofState (EXTM :=>: VAL)
> getFakeMother = do
>    r <- getFakeRef
>    inScope <- getInScope
>    let tm = P r $:$ (paramSpine inScope)
>    return $ tm :=>: evTm tm
