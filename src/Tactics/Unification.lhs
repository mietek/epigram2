\section{Unification}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Tactics.Unification where

> import Prelude hiding (any, elem)

> import Data.Foldable
> import qualified Data.Monoid as M

> import Evidences.Tm
> import Evidences.Eval

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

\subsection{Solving flex-rigid problems}

The |solveHole| command solves a flex-rigid problem by filling in the reference
(which must be a hole) with the given term, which must contain no defined
references. It records the current location in the proof state (but not the
cursor position) and returns there afterwards.

> solveHole :: REF -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole ref tm = do
>     here <- getCurrentName
>     r <- solveHole' ref [] tm
>     cursorBottom
>     goTo here
>     return r

The |solveHole'| command actually fills in the hole, accumulating a list of
dependencies (references the solution depends on) as it passes them. It moves
the dependencies to before the hole by creating new holes earlier in
the proof state and inserting a news bulletin that solves the old dependency
holes with the new ones.

> solveHole' :: REF -> [(REF, INTM)] -> INTM -> ProofState (EXTM :=>: VAL)
> solveHole' ref@(name := HOLE _ :<: _) deps tm = do
>     es <- getEntriesAbove
>     case es of
>         B0      -> goOutBelow >> cursorUp >> solveHole' ref deps tm
>         _ :< e  -> pass e
>   where
>     pass :: Entry Bwd -> ProofState (EXTM :=>: VAL)
>     pass (EDEF def@(defName := _) _ _ _ _ _)
>       | name == defName && occurs def = throwError' $
>           err "solveHole: you can't define something in terms of itself!"
>       | name == defName = do
>           cursorUp
>           news <- makeDeps deps []
>           cursorDown
>           goIn
>           putNewsBelow news
>           let (tm', _) = tellNews news tm
>           tm'' <- bquoteHere (evTm tm')
>           giveOutBelow tm''
>       | occurs def = do
>           goIn
>           ty :=>: _ <- getGoal "solveHole"
>           solveHole' ref ((def, ty):deps) tm
>       | otherwise = goIn >> solveHole' ref deps tm
>     pass (EPARAM param _ _ _ _)
>       | occurs param = throwError' $
>             err "solveHole: param" ++ errRef param ++ err "occurs illegally."
>       | otherwise = cursorUp >> solveHole' ref deps tm
>     pass (EModule modName _) = goIn >> solveHole' ref deps tm
>
>     occurs :: REF -> Bool
>     occurs ref = any (== ref) tm || ala M.Any foldMap (any (== ref) . snd) deps

>     makeDeps :: [(REF, INTM)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((name := HOLE k :<: tyv, ty) : deps) news = do
>         let (ty', _) = tellNews news ty
>         makeKinded Nothing k (fst (last name) :<: ty')
>         EDEF ref _ _ _ _ _ <- getEntryAbove
>         makeDeps deps ((name := DEFN (NP ref) :<: tyv, GoodNews) : news)
>     makeDeps _ _ = throwError' $ err "makeDeps: bad reference kind! Perhaps "
>         ++ err "solveHole was called with a term containing unexpanded definitions?"

> solveHole' ref _ _ = throwError' $ err "solveHole:" ++ errRef ref
>                                           ++ err "is not a hole."


\adam{where should this live?}

> stripShared :: NEU -> ProofState REF
> stripShared n = getInScope >>= stripShared' n
>   where
>     stripShared' :: NEU -> Entries -> ProofState REF
>     stripShared' (P ref@(_ := HOLE Hoping :<: _)) B0 = return ref
>     stripShared' (n :$ A (NP r)) (es :< EPARAM paramRef _ _ _ _)
>         | r == paramRef                      = stripShared' n es
>     stripShared' n (es :< EDEF _ _ _ _ _ _)  = stripShared' n es
>     stripShared' n (es :< EModule _ _)       = stripShared' n es
>     stripShared' n es = do
>       -- |proofTrace $ "stripShared: fail on " ++ show n|
>       throwError' $ err "stripShared: fail on" ++ errVal (N n)
