\section{Unification}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Tactics.Unification where

> import Prelude hiding (any, elem, exp)

> import Data.Foldable
> import qualified Data.Monoid as M

> import Control.Applicative

> import Evidences.Tm
> import Evidences.ErrorHandling

> import DisplayLang.Name

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
> import Kit.NatFinVec
> import Kit.MissingLibrary

%endif

\subsection{Solving flex-rigid problems}

The |solveHole| command solves a flex-rigid problem by filling in the reference
(which must be a hole) with the given term, which must contain no defined
references. It records the current location in the proof state (but not the
cursor position) and returns there afterwards.

> solveHole :: Name -> EXP -> ProofState EXP
> solveHole ref tm = do
>     here <- getCurrentName
>     solveHole' ref [] tm <* cursorBottom <* goTo here 

The |solveHole'| command actually fills in the hole, accumulating a list of
dependencies (references the solution depends on) as it passes them. It moves
the dependencies to before the hole by creating new holes earlier in
the proof state and inserting a news bulletin that solves the old dependency
holes with the new ones.

> solveHole' :: Name -> [(DEF, Tip)] -> EXP -> ProofState EXP
> solveHole' name deps tm = do
>     es <- getEntriesAbove
>     case es of
>         B0      -> goOutBelow >> cursorUp >> solveHole' name deps tm
>         _ :< e  -> pass e
>   where
>     pass :: Entry Bwd -> ProofState EXP
>     pass (EDef def@(DEF defName _ _) dev _)
>       | name == defName && occursD defName = throwError' $
>           err "solveHole: you can't define something in terms of itself!"
>       | name == defName = do
>           cursorUp
>           news <- makeDeps deps NONEWS
>           cursorDown
>           goIn
>           putNewsBelow news
>           let (tm', _) = tellNews news tm
>               tm'' = exp (ev tm')
>           (| (\ d -> D d S0 (defOp d)) (giveOutBelow tm'') |)
>       | occursD defName = do
>           goIn
>           solveHole' name ((def, devTip dev):deps) tm
>       | otherwise = goIn >> solveHole' name deps tm
>     pass (EParam _ s _ l)
>       | occursP l = throwError' $
>             err "solveHole: param" ++ err s ++ err "occurs illegally."
>       | otherwise = cursorUp >> solveHole' name deps tm
>     pass (EModule _ _) = goIn >> solveHole' name deps tm
>
>     occursD :: Name -> Bool
>     occursD name = occurs (Just name) [] [] tm
>     occursP :: Int -> Bool
>     occursP l = occurs Nothing [l] [] tm

>     makeDeps :: [(DEF, Tip)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((old, Unknown ty k) : deps) news = do
>         let (ty', _) = tellNews news ty
>         makeKinded Nothing k (fst (last name) :<: ty')
>         EDef def _ _ <- getEntryAbove
>         let op = Emit (D def S0 (defOp def))
>         makeDeps deps (addGirlNews (old{defOp = op}, GoodNews) news)
>     makeDeps _ _ = throwError' $ err "makeDeps: bad reference kind! Perhaps "
>         ++ err "solveHole was called with a term containing unexpanded definitions?"

> {-

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

> -}

What fresh hell is this:

> occurs :: Maybe Name -> [Int] -> [Fin {n}] -> Tm {p, s, n} -> Bool 
> occurs n p v (L g x b) = let (p', v') = occursEnv n p v g in occurs n p' (map Fs v') b
> occurs n p v (LK b) = occurs n p v b
> occurs n p v (c :- es) = any (occurs n p v) es
> occurs n p v (f :$ as) = (occurs n p v f) || any (any (occurs n p v)) as
> occurs n p v (D def ss o) = any (defName def ==) n || any (occurs n [] []) ss
> occurs n p v (V i) = elem i v
> occurs n p v (P (l , s , t)) = elem l p
> occurs n p v (e :/ t) = let (p', v') = occursEnv n p v e in occurs n p' v' t

> occursEnv :: Maybe Name -> [Int] -> [Fin m] -> Env {m} {n} -> ([Int] , [Fin {n}]) 
> occursEnv n p v (lenv,ienv) = (occursLEnv n p v lenv, occursIEnv n p v ienv)

> occursLEnv :: Maybe Name -> [Int] -> [Fin {n}] -> Maybe [Tm {Body, Exp, n}] -> [Int]
> occursLEnv n p v Nothing = p
> occursLEnv n p v (Just ts) = 
>   map fst (filter (\ x -> occurs n p v (snd x)) (zip  [0..] ts))

> occursIEnv :: Maybe Name -> [Int] -> [Fin {m}] -> IEnv {m, n} -> [Fin {n}] 
> occursIEnv n p v INix = []
> occursIEnv n p v INil = v
> occursIEnv n p v (ienv :<<: t) | occurs n p [] t = 
>   Fz : (map Fs (occursIEnv n p v ienv)) 
> occursIEnv n p v (ienv :<<: t) = map Fs (occursIEnv n p v ienv)
