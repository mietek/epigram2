\section{The Scheduler}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.Scheduler where

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.Developments
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Tactics.Information

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.Elaborator
> import Elaboration.Unification

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


> startScheduler :: ProofState ()
> startScheduler = cursorTop >> scheduler 0

> scheduler :: Int -> ProofState ()
> scheduler n = do
>     cs <- getDevCadets
>     case cs of
>         F0      -> if n == 0 then return () else goOutProperly >> scheduler (n-1)
>         E _ _ (Boy _) _ :> _  -> cursorDown >> scheduler n
>         E ref _ (Girl _ (_, Suspended tt prob, _) _) _ :> _
>           | isUnstable prob -> do
>             cursorDown
>             goIn            
>             mtt <- resumeEProb
>             case mtt of
>                 Just (tm :=>: _) -> do
>                     proofTrace "scheduler: elaboration done."
>                     give' tm
>                     cursorTop
>                     scheduler (n+1)
>                 Nothing -> do
>                     proofTrace "scheduler: elaboration suspended."
>                     goOutProperly
>                     cursorTop
>                     scheduler n

>         _ :> _ -> cursorDown >> goIn >> cursorTop >> scheduler (n+1)


> resumeEProb :: ProofState (Maybe (INTM :=>: VAL))
> resumeEProb = do
>     Suspended (ty :=>: tyv) prob <- getDevTip
>     putDevTip (Unknown (ty :=>: tyv))
>     mn <- getMotherName
>     proofTrace $ "Resuming elaboration on " ++ showName mn ++ ":  \n" ++ show prob
>     resume (ty :=>: tyv) prob
>   where
>     resume :: (INTM :=>: VAL) -> EProb -> ProofState (Maybe (INTM :=>: VAL))
>     resume _ (ElabDone tt) = return $ Just (maybeEval tt)
>     resume (ty :=>: tyv) (ElabProb tm) =
>         return . ifSnd =<< runElab True (tyv :>: makeElab (Loc 0) (tyv :>: tm))
>     resume (ty :=>: tyv) (ElabInferProb tm) =
>         return . ifSnd =<< runElab True (tyv :>: makeElabInfer (Loc 0) tm)
>     resume (ty :=>: tyv) (WaitCan (tm :=>: Just (C v)) prob) = resume (ty :=>: tyv) prob
>     resume (ty :=>: tyv) (WaitCan (tm :=>: Nothing) prob) = resume (ty :=>: tyv) (WaitCan (tm :=>: Just (evTm tm)) prob)
>     resume _ prob@(WaitCan (tm :=>: _) _) = do
>         proofTrace $ "Suspended waiting for " ++ show tm ++ " to become canonical."
>         suspendMe prob
>         return Nothing
>     resume _ (WaitSolve ref@(_ := HOLE _ :<: _) stt prob) = do
>         suspendMe prob
>         tm <- bquoteHere (valueOf . maybeEval $ stt) -- force definitional expansion
>         solveHole ref tm
>         return Nothing
>     resume tt (WaitSolve ref@(_ := DEFN tmv' :<: ty) stt prob) = do
>         eq <- withNSupply $ equal (ty :>: (valueOf . maybeEval $ stt , tmv'))
>         if eq
>             then  resume tt prob
>             else  throwError' $ err "resume: hole has been solved inconsistently! We should do something clever here."
>                 

> ifSnd :: (a, Bool) -> Maybe a
> ifSnd (a,  True)   = Just a
> ifSnd (_,  False)  = Nothing


> elmCT :: ExDTmRN -> ProofState String
> elmCT tm = do
>     suspend ("elab" :<: sigSetTM :=>: sigSetVAL) (ElabInferProb tm)
>     startScheduler
>     infoElaborate (DP [("elab", Rel 0)] ::$ [])

> import -> CochonTactics where
>   : unaryExCT "elm" elmCT "elm <term> - elaborate <term>, stabilise and print type-term pair."