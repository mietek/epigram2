\section{Making Definitions}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Definition where

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import ProofState.Structure.Developments

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.Lifting
> import ProofState.Interface.Name
> import ProofState.Interface.ProofKit

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.Eval

%endif


The |make| command adds a named goal of the given type above the
cursor. The meat is actually in |makeKinded|, below.

> make :: (String :<: INTM) -> ProofState (EXTM :=>: VAL)
> make = makeKinded Nothing Waiting

When making a new definition, the reference to this definition bears a
\emph{hole kind}
(Section~\ref{subsec:Evidences.Tm.references}). User-generated goals
are of kind |Waiting|: waiting for the user to solve it (or, if lucky,
an automation tool could nail it down). For making these kind of
definition, we will use the |make| command above. However, during
Elaboration for instance (Section~\ref{sec:Elaborator.Elaborator}),
the proof system will insert goals itself, with a somewhat changing
mood such as |Hoping| or |Crying|.

> makeKinded :: Maybe String ->  HKind -> (String :<: INTM) -> 
>                                ProofState (EXTM :=>: VAL)
> makeKinded manchor holeKind (name :<: ty) = do
>     -- Check that the type is indeed a type
>     _ :=>: tyv <- checkHere (SET :>: ty) 
>                     `pushError`  
>                     (err "make: " ++ errTm (DTIN ty) ++ err " is not a set.")
>     -- Make a name for the goal, from |name|
>     nsupply <- getDevNSupply
>     goalName <- pickName "Goal" name
>     let  n  =  mkName nsupply goalName
>     -- Make a reference for the goal, with a lambda-lifted type
>     inScope <- getInScope
>     let  liftedTy  =  liftType inScope ty
>          ref       =  n := HOLE holeKind :<: evTm liftedTy
>     -- Make an entry for the goal, with an empty development
>     let dev = Dev { devEntries       =  B0
>                   , devTip           =  Unknown (ty :=>: tyv)
>                   , devNSupply       =  freshNSpace nsupply goalName
>                   , devSuspendState  =  SuspendNone }
>     -- Put the entry in the proof context
>     putDevNSupply $ freshName nsupply
>     putEntryAbove $ EDEF ref (last n) LETG dev liftedTy manchor
>     -- Return a reference to the goal
>     return $ applySpine ref inScope
