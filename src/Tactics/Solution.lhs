\section{Solution Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Tactics.Solution where

> import Control.Applicative
> import Data.Traversable

> import Kit.BwdFwd

> import ProofState.Developments
> import ProofState.ProofContext
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Elaborator
> import DisplayLang.Naming

> import NameSupply.NameSupply

> import Evidences.Rules
> import Evidences.Tm

> import Tactics.Information

%endif

> solveHole :: REF -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole (name := HOLE _ :<: _) tm = do
>     proofTrace ("Solving " ++ showName name ++ " with " ++ show tm ++ ".")
>     here <- getMotherName
>     goTo name
>     r <- give' tm
>     goTo here
>     return r


> elabSolveHole :: RelName -> InDTmRN -> ProofState (EXTM :=>: VAL)
> elabSolveHole rn tm = do
>     ref <- resolveHere rn
>     tt <- elaborate False (pty ref :>: tm)
>     solveHole ref (termOf tt)


> import -> CochonTactics where
>     : simpleCT
>         "solve"
>         (| (| (B0 :<) tokenName |) :< tokenInTm |)
>         (\ [ExArg (DP rn), InArg tm] -> elabSolveHole rn tm >> return "Solved.")
>         "solve <name> <term> - solves the hole <name> with <term>."