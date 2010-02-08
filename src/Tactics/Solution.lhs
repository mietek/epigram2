\section{Solution Tactics}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators #-}

> module Tactics.Solution where

> import Prelude hiding (any)

> import Control.Applicative
> import Data.Foldable
> import Data.Maybe
> import Data.Monoid
> import Data.Traversable

> import Kit.BwdFwd

> import ProofState.Developments
> import ProofState.News
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


> solveHole :: REF -> [(REF, INTM)] -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole ref@(name := HOLE _ :<: _) deps tm = do
>     es <- getDevEntries
>     case es of
>         B0      -> goOutProperly >> cursorUp >> solveHole ref deps tm
>         _ :< e  -> pass e
>   where
>     pass :: Entry Bwd -> ProofState (EXTM :=>: VAL)
>     pass (E girl@(girlName := _) _ (Girl LETG _ _) girlTm)
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
>       | occurs girl = goIn >> solveHole ref ((girl, girlTm):deps) tm
>       | otherwise = goIn >> solveHole ref deps tm
>     pass (E boy _ (Boy _) _)
>       | occurs boy = throwError' $
>             err "solveHole: boy" ++ errRef boy ++ err "occurs illegally."
>       | otherwise = cursorUp >> solveHole ref deps tm
>     pass (M modName _) = goIn >> solveHole ref deps tm
>
>     occurs :: REF -> Bool
>     occurs ref = any (== ref) tm || getAny (foldMap (Any . any (== ref) . snd) deps)
>             
>     makeDeps :: [(REF, INTM)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((name := HOLE _ :<: tyv, ty): deps) news = do
>         let (ty', _) = tellNews news ty
>         rtm :=>: rv <- make (fst (last name) :<: ty')
>         makeDeps deps ((name := DEFN rv :<: tyv, GoodNews) : news)


> elabSolveHole :: RelName -> InDTmRN -> ProofState (EXTM :=>: VAL)
> elabSolveHole rn tm = do
>     (ref, spine, _) <- elabResolve rn
>     _ :<: ty <- inferHere (P ref $:$ spine)
>     tt <- elaborate False (ty :>: tm)
>     solveHole ref [] (termOf tt)


> import -> CochonTactics where
>     : simpleCT
>         "solve"
>         (| (| (B0 :<) tokenName |) :< tokenInTm |)
>         (\ [ExArg (DP rn), InArg tm] -> elabSolveHole rn tm >> return "Solved.")
>         "solve <name> <term> - solves the hole <name> with <term>."