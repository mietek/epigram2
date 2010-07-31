\section{The |ProofState| Kit}
\label{sec:proof_state_kit}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.ProofKit where

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

\question{There are some serious re-ordering of functions to be done
here, in order to improve the narrative.}


\subsection{Asking for Evidence}

A |ProofState| is almost a |NameSupplier|, but it cannot fork the
name supply.

> instance NameSupplier (ProofStateT e) where
>     freshRef (s :<: ty) f = do
>         nsupply <- getDevNSupply
>         freshRef (s :<: ty) (\ref nsupply' -> do
>             putDevNSupply nsupply'
>             f ref
>           ) nsupply
>
>     forkNSupply = error "ProofState does not provide forkNSupply"
>     
>     askNSupply = getDevNSupply

We also provide an operator to lift functions from a name supply
to proof state commands.

> withNSupply :: (NameSupply -> x) -> ProofState x
> withNSupply f = getDevNSupply >>= return . f

\begin{danger}[Read-only name supply]

Note that this function has no way to return an updated name supply to
the proof context, so it must not leave any references around when it
has finished.

\end{danger}


The |bquoteHere| command $\beta$-quotes a term using the current name supply.

> bquoteHere :: Tm {d, VV} REF -> ProofState (Tm {d, TT} REF)
> bquoteHere tm = withNSupply $ bquote B0 tm


> runCheckHere :: (ErrorTok e -> ErrorTok DInTmRN) -> Check e a -> ProofState a
> runCheckHere f c = do
>     me <- withNSupply $ liftError' f . typeCheck c
>     lift me


Similarly, |checkHere| type-checks a term using the local name supply...

> checkHere :: (TY :>: INTM) -> ProofState (INTM :=>: VAL)
> checkHere tt = runCheckHere (fmap DTIN) $ check tt

... and |inferHere| infers the type of a term using the local name supply.

> inferHere :: EXTM -> ProofState (VAL :<: TY)
> inferHere tm = runCheckHere (fmap DTIN) $ infer tm



The |validateHere| performs some checks on the current location, which
may be useful for paranoia purposes.

> validateHere :: ProofState ()
> validateHere = do
>     m <- getCurrentEntry
>     case m of
>         CDefinition _ (_ := DEFN tm :<: ty) _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: girl type failed to type-check: SET does not admit"
>                              ++ errTyVal (ty :<: SET))
>             tm' <- bquoteHere tm
>             checkHere (ty :>: tm')
>                 `pushError`  (err "validateHere: definition failed to type-check:"
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "does not admit"
>                              ++ errTyVal (tm :<: ty))
>             return ()
>         CDefinition _ (_ := HOLE _ :<: ty) _ _ -> do
>             ty' <- bquoteHere ty
>             checkHere (SET :>: ty')
>                 `pushError`  (err "validateHere: hole type failed to type-check: SET does not admit" 
>                              ++ errTyVal (ty :<: SET))
>             return ()
>         _ -> return ()


> withGoal :: (VAL -> ProofState ()) -> ProofState ()
> withGoal f = do
>   (_ :=>: goal) <- getGoal "withGoal"
>   f goal








\subsection{Construction Commands}

Various commands yield an |EXTM :=>: VAL|, and we sometimes need to convert
this to an |INTM :=>: VAL|:

> neutralise :: Monad m => (EXTM :=>: VAL) -> m (INTM :=>: VAL)
> neutralise (n :=>: v) = return (N n :=>: v)





> ignore :: ProofState a -> ProofState ()
> ignore f = do
>     f
>     return ()

     



The |getFakeMother| command returns a neutral application of a fake reference
that represents the mother of the current location. Note that its type is
$\lambda$-lifted over its great uncles, but it is then applied to them (as
shared parameters).

> getFakeRef :: ProofState REF
> getFakeRef = do
>    CDefinition _  (mnom := HOLE _ :<: ty) _ _ <- getCurrentEntry
>    return (mnom := FAKE :<: ty)

> getFakeMother :: ProofState (EXTM :=>: VAL)
> getFakeMother = do
>    r <- getFakeRef
>    inScope <- getInScope
>    let tm = P r $:$ (paramSpine inScope)
>    return $ tm :=>: evTm tm





When the current location or one of its children has suspended, we need to
update the outer layers.

> grandmotherSuspend :: SuspendState -> ProofState ()
> grandmotherSuspend ss = getLayers >>= putLayers . help ss
>   where
>     help :: SuspendState -> Bwd Layer -> Bwd Layer
>     help ss B0 = B0
>     help ss (ls :< l) = help ss' ls :< l{laySuspendState = ss'}
>       where ss' = min ss (laySuspendState l)