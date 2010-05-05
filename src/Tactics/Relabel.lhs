\section{Relabelling}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, TupleSections #-}

> module Tactics.Relabel where

> import Control.Applicative

> import Evidences.Rules
> import Evidences.Tm

> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm

> import Elaboration.ElabMonad
> import Elaboration.RunElab
> import Elaboration.Elaborator
> import Elaboration.Unification
> import Elaboration.Scheduler

> import Kit.MissingLibrary

%endif

The |relabel| command changes the names of the pattern variables in a programming
problem. It takes a list of unelaborated arguments corresponding to the arguments
of the programming problem, matches them against the existing arguments to determine
the renaming, and refines the proof state appropriately.

\question{At present, the arguments must contain hoping holes when elaborated, so
they have to contain underscores in the display synax. How can we fix this?
The programming problem should tell us which argument positions contain pattern
variables, but how do we look inside terms to find them? We could somehow extend
the elaborator to report unresolved names instead of failing, but suspension might
cause issues.}

> relabel :: [InDTmRN] -> ProofState ()
> relabel ts = do
>     _ :=>: LABEL (N l) ty <- getHoleGoal
>     let Just (r, as) = splitSpine l
>     (n, sols) <- matchArgs (pty r) (P r) as ts []
>     ty' <- bquoteHere ty
>     g :=>: _ <- make ("g" :<: LABEL (N n) ty')
>     suspendMe =<< makeWait sols (N g)
>     goOutProperly
>     startScheduler
>     startScheduler -- TODO: fix scheduler bug that makes this necessary
>     startScheduler
>     nextGoal
>   where
>     splitSpine :: NEU -> Maybe (REF, [VAL])
>     splitSpine (P r) = return (r, [])
>     splitSpine (n :$ A a) = do
>         (r, as) <- splitSpine n
>         return (r, as ++ [a])
>     splitSpine _ = (|)

>     matchArgs :: TY -> EXTM -> [VAL] -> [InDTmRN] -> [(REF, VAL)] -> ProofState (EXTM, [(REF, VAL)])
>     matchArgs _ n []  [] sols  = return (n, sols)
>     matchArgs _ _ []  _  _     = throwError' $ err "relabel: too many arguments!"
>     matchArgs _ _ _   [] _     = throwError' $ err "relabel: too few arguments!"
>     matchArgs (PI s t) n (a:as) (w : ws) sols = do
>         wtm :=>: wv <- elaborate (Loc 0) (s :>: w)
>         subst <- valueMatch (s :>: (wv, a))
>         matchArgs (t $$ A a) (n :$ A wtm) as ws (sols ++ subst)
>     matchArgs ty n as ts _ = throwError' $ err "relabel: unmatched\nty ="
>                              ++ errTyVal (ty :<: SET)
>                              ++ err "\nn =" ++ errInTm (N n)
>                              ++ err "\nas =" ++ map UntypedVal as
>                              ++ err "\nts =" ++ map UntypedTm ts         


> import -> CochonTactics where
>   : simpleCT "relabel" (| bwdList (some (|InArg (sizedInDTm minBound)|)) |)
>       (\ as -> relabel (map argToIn as) >> return "Relabelled.")
>       "relabel <args> - changes names of arguments in label"