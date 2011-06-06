\section{Making Definitions}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE FlexibleInstances, TypeOperators, TypeSynonymInstances,
>              GADTs, RankNTypes #-}

> module ProofState.Interface.Definition where

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary

> import ProofState.Structure.Developments

> import ProofState.Edition.Scope
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

< import ProofState.Interface.Lifting

> import ProofState.Interface.Name

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Module

> import DisplayLang.DisplayTm

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.ErrorHandling

%endif

> {-

> make :: (String :<: EXP) -> ProofState EXP
> make (s :<: ty) = do
>     makeModule s
>     goIn
>     e <- moduleToGoal ty
>     goOut
>     return e

> -}

The |make| command adds a named goal of the given type above the
cursor. The meat is actually in |makeKinded|, below.

> make :: (String :<: TY) -> ProofState EXP
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

> makeKinded :: Maybe String ->  HKind -> (String :<: TY) -> 
>                                ProofState EXP
> makeKinded manchor holeKind (name :<: ty) = do
>     -- Check that the type is indeed a type
>     checkHere (SET :>: ty) 
>                     `pushError`  
>                     (err "make: " ++ errTm ty ++ err " is not a set.")
>     -- Make a name for the goal, from |name|
>     nsupply <- getDevNSupply
>     lev <- getDevLev
>     goalName <- pickName "Goal" name
>     let  n  =  mkName nsupply goalName
>     -- Make a reference for the goal, with a lambda-lifted type
>     inScope <- getInScope
>     let  binScope  = boys inScope
>          liftedTy = bwdVec (fmap (\(_, s, t) -> (s, t)) (boys inScope))
>                             (\ n ys -> piLift n ys) ty
>          def = DEF n liftedTy Hole -- (eats (trail (fmap (\(_,s,_) -> s) (boys inScope))) Hole)

>     -- Make an entry for the goal, with an empty development
>     let dev = Dev { devEntries       =  B0
>                   , devTip           =  Unknown ty holeKind
>                   , devNSupply       =  freshNSpace nsupply goalName
>                   , devSuspendState  =  SuspendNone
>                   , devLevelCount    =  lev }
>     -- Put the entry in the proof context
>     putDevNSupply $ freshen nsupply
>     putEntryAbove $ EDef def dev Nothing
>     -- Return a reference to the goal
>     return $  D def S0 (defOp def) $$$ fmap (\x -> A (P x :$ B0)) binScope
>  where 
>    boys :: Entries -> Bwd (Int, String, TY)
>    boys B0 = B0
>    boys (es :< EParam _ s t l) =  boys es :< (l, s, t)
>    boys (es :< _) =  boys es 

