\section{Solution Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Tactics.Solution where

> import Prelude hiding (any)

> import Data.Foldable
> import Data.Monoid

> import Evidences.Rules
> import Evidences.Tm

> import ProofState.Developments
> import ProofState.News
> import ProofState.ProofState
> import ProofState.ProofKit

> import DisplayLang.DisplayTm
> import DisplayLang.Naming

> import Elaboration.Elaborator

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

> forceHole :: REF -> INTM -> ProofState (EXTM :=>: VAL)
> forceHole (name := HOLE _ :<: _) tm = do
>     proofTrace ("Forcing " ++ showName name ++ " to be " ++ show tm ++ ".")
>     here <- getMotherName
>     goTo name
>     r <- give' tm
>     goTo here
>     return r

> solveHole :: REF -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole ref tm = do
>     here <- getMotherName
>     r <- solveHole' ref [] tm
>     cursorBottom
>     goTo here
>     return r

> solveHole' :: REF -> [(REF, INTM)] -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole' ref@(name := HOLE _ :<: _) deps tm = do
>     es <- getDevEntries
>     case es of
>         B0      -> goOutProperly >> cursorUp >> solveHole' ref deps tm
>         _ :< e  -> pass e
>   where
>     pass :: Entry Bwd -> ProofState (EXTM :=>: VAL)
>     pass (E girl@(girlName := _) _ (Girl LETG _ _) girlTyTm)
>       | name == girlName && occurs girl = throwError' $
>           err "solveHole: you can't define something in terms of itself!"
>       | name == girlName = do
>           cursorUp
>           news <- makeDeps deps []
>           cursorDown
>           goIn
>           insertCadet news
>           let (tm', _) = tellNews news tm
>           tm'' <- bquoteHere (evTm tm')
>           give tm''
>       | occurs girl = goIn >> solveHole' ref ((girl, girlTyTm):deps) tm
>       | otherwise = goIn >> solveHole' ref deps tm
>     pass (E boy _ (Boy _) _)
>       | occurs boy = throwError' $
>             err "solveHole: boy" ++ errRef boy ++ err "occurs illegally."
>       | otherwise = cursorUp >> solveHole' ref deps tm
>     pass (M modName _) = goIn >> solveHole' ref deps tm
>
>     occurs :: REF -> Bool
>     occurs ref = any (== ref) tm || ala Any foldMap (any (== ref) . snd) deps

>     makeDeps :: [(REF, INTM)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((name := HOLE _ :<: tyv, ty) : deps) news = do
>         let (ty', _) = tellNews news ty
>         _ :=>: rv <- make (fst (last name) :<: ty')
>         makeDeps deps ((name := DEFN rv :<: tyv, GoodNews) : news)
>     makeDeps _ _ = throwError' $ err "makeDeps: bad reference kind! Perhaps "
>         ++ err "solveHole was called with a term containing unexpanded definitions?"

> solveHole' ref _ _ = throwError' $ err "solveHole:" ++ errRef ref
>                                           ++ err "is not a hole."

> elabSolveHole :: RelName -> InDTmRN -> ProofState (EXTM :=>: VAL)
> elabSolveHole rn tm = do
>     (ref, spine, _) <- elabResolve rn
>     _ :<: ty <- inferHere (P ref $:$ spine)
>     _ :=>: tv <- elaborate False (ty :>: tm)
>     tm' <- bquoteHere tv -- force definitional expansion
>     solveHole ref tm'


> import -> CochonTactics where
>     : simpleCT
>         "solve"
>         (| (| (B0 :<) tokenName |) :< tokenInTm |)
>         (\ [ExArg (DP rn ::$ []), InArg tm] -> elabSolveHole rn tm >> return "Solved.")
>         "solve <name> <term> - solves the hole <name> with <term>."