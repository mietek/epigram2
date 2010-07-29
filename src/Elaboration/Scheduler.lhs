\section{The Scheduler}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Elaboration.Scheduler where

> import Control.Applicative

> import NameSupply.NameSupply

> import Evidences.Tm
> import Evidences.Rules

> import Features.Features ()

> import ProofState.Structure.Developments

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.Lifting
> import ProofState.Interface.ProofKit

> import DisplayLang.Name

> import Elaboration.ElabMonad
> import Elaboration.MakeElab
> import Elaboration.RunElab
> import Elaboration.Unification

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

Handling elaboration essentially requires writing an operating system. Having
defined how to execute processes in section~\ref{sec:elaborator}, we now turn
our attention to process scheduling. The scheduler is called when an
elaboration process yields (either halting after solving its goal, halting
with an error, or suspending work until later). It searches downwards in the
proof state for unstable elaboration problems and executes any it finds.

When the scheduler is started, all problems before the working location should
be stable, but there may be unstable problems in the current location and below
it. The |startScheduler| command runs the scheduler from the current location,
so it will stabilise the children and return to where it started.

> startScheduler :: ProofState ()
> startScheduler = getMotherName >>= scheduler

In general, the scheduler might have to move non-locally (e.g. in order to solve
goals elsewhere in the proof state), so it keeps track of a target location to
return to. When |scheduler| is called, it checks to see if there might be any
suspended problems below the current location. If so, it resets the suspend
state and starts searching from the top of the development. If not, it calls
|schedulerDone| to move out or terminate as appropriate.

> scheduler :: Name -> ProofState ()
> scheduler n = do
>     ss <- (|devSuspendState getDev|)
>     case ss of
>         SuspendUnstable  -> do  putDevSuspendState SuspendNone
>                                 cursorTop
>                                 schedulerContinue n
>         _                -> schedulerDone n

The |schedulerContinue| command processes the cadets. The suspend state should
describe the entries above the cursor. If there are no cadets to search, we are
done. If we find a boy, we simply move past it, because it cannot have a
suspended problem attached. If we find a module or a girl, we enter it, try to
resume its mother, then search its children from the top.

> schedulerContinue :: Name -> ProofState ()
> schedulerContinue n = do
>     cs <- getDevCadets
>     case cs of
>         F0                    -> schedulerDone n
>         E _ _ (Boy _) _ :> _  -> cursorDown >> schedulerContinue n
>         _ :> _                -> do
>             cursorDown
>             goIn
>             resumeMother
>             scheduler n


Once done, the |schedulerDone| command checks if this is the target location.
If so, we stop; otherwise, we resume the mother and continue searching.

> schedulerDone :: Name -> ProofState ()
> schedulerDone n = do
>         mn <- getMotherName
>         case mn of
>             _ | mn == n  -> cursorBottom
>             []           -> error "scheduler: got lost!"
>             _            -> do
>                 b <- resumeMother
>                 if b  then scheduler n
>                       else do
>                           goOutProperly
>                           schedulerContinue n


The |resumeMother| command checks for an unstable elaboration problem on the
mother of the current location, and resumes elaboration if it finds one. If
elaboration succeeds, it gives the resulting term. It returns whether an
elaboration process was resumed (not whether the process succeeded).

> resumeMother :: ProofState Bool
> resumeMother = do
>   tip <- getDevTip
>   case tip of
>     Suspended (ty :=>: tyv) prob | isUnstable prob -> do
>         putDevTip (Unknown (ty :=>: tyv))
>         mn <- getMotherName
>         schedTrace $ "scheduler: resuming elaboration on " ++ showName mn
>                           ++ ":  \n" ++ show prob
>         mtt <- resume (ty :=>: tyv) prob
>         case mtt of
>             Just tt  ->  give' (termOf tt)
>                      >>  schedTrace "scheduler: elaboration done."
>             Nothing  ->  schedTrace "scheduler: elaboration suspended."
>         return True
>     _ -> return False


Given a (potentially, but not necessarily, unstable) elaboration problem for the
current location, we can |resume| it to try to produce a term. If this suceeds,
the cursor will be in the same location, but if it fails (i.e.\ the problem has
been suspended) then the cursor could be anywhere earlier in the proof state.

> resume :: (INTM :=>: VAL) -> EProb -> ProofState (Maybe (INTM :=>: VAL))
> resume _ (ElabDone tt) = return . Just . maybeEval $ tt
> resume (ty :=>: tyv) ElabHope = 
>     return . ifSnd =<< runElabHope True tyv
> resume (ty :=>: tyv) (ElabProb tm) = 
>     return . ifSnd =<< runElab True (tyv :>: makeElab (Loc 0) tm)
> resume (ty :=>: tyv) (ElabInferProb tm) =
>     return . ifSnd =<< runElab True (tyv :>: makeElabInfer (Loc 0) tm)
> resume (ty :=>: tyv) (WaitCan (tm :=>: Just (C v)) prob) =
>     resume (ty :=>: tyv) prob
> resume (ty :=>: tyv) (WaitCan (tm :=>: Nothing) prob) =
>     resume (ty :=>: tyv) (WaitCan (tm :=>: Just (evTm tm)) prob)
> resume _ prob@(WaitCan (tm :=>: _) _) = do
>     schedTrace $ "Suspended waiting for " ++ show tm ++ " to become canonical."
>     suspendMe prob
>     return Nothing
> resume _ (WaitSolve ref@(_ := HOLE _ :<: _) stt prob) = do
>     suspendMe prob
>     mn <- getMotherName
>     tm <- bquoteHere (valueOf . maybeEval $ stt) -- force definitional expansion
>     solveHole' ref [] tm -- takes us to who knows where
>     return Nothing

If we have a |WaitSolve| problem where the hole has already been solved with
something else, we need to check the solution is compatible. \question{How
can we reorganise things to use propositional rather than definitional
equality here?}

> resume tt (WaitSolve ref@(_ := DEFN tmv' :<: ty) stt prob) = do
>     aus   <- getGreatAuncles
>     sibs  <- getDevEntries
>     let  stt'  = maybeEval stt
>          stm   = parBind aus sibs (termOf stt')
>     eq <- withNSupply $ equal (ty :>: (evTm stm, tmv'))
>     if eq
>         then  resume tt prob
>         else  throwError' $ err "resume: hole" ++ errRef ref ++
>                    err "has been solved with" ++ errTyVal (tmv' :<: ty) ++
>                    err "but I wanted to solve it with" ++
>                            errTyVal (valueOf stt' :<: ty)

> resume tt (ElabSchedule prob) = resume tt prob


> ifSnd :: (a, Bool) -> Maybe a
> ifSnd (a,  True)   = Just a
> ifSnd (_,  False)  = Nothing


Trace messages from the scheduler are essential for debugging but annoying
otherwise, so we can enable or disable them at compile time.

> schedTrace :: String -> ProofState ()
> schedTrace s = if schedTracing then proofTrace s else return ()

> schedTracing = False