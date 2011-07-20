\section{Unification}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Tactics.Unification where

> import Prelude hiding (any, elem, exp)

> import Data.List hiding (any, elem)
> import Data.Foldable hiding (foldr)
> import qualified Data.Monoid as M

> import Control.Applicative

> import Evidences.Tm
> import Evidences.EtaQuote
> import Evidences.ErrorHandling
> import Evidences.News

> import DisplayLang.Name

> import ProofState.Structure
> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary

%endif

\subsection{Solving flex-rigid problems}

The |solveHole| command solves a flex-rigid problem by filling in the reference
(which must be a hole) with the given term, which must contain no defined
references. It records the current location in the proof state (but not the
cursor position) and returns there afterwards.

> solveHole :: Name -> (TY :>: EXP) -> ProofState EXP
> solveHole ref tm = do
>     here <- getCurrentName
>     solveHole' ref [] tm <* cursorBottom <* goTo here 

The |solveHole'| command actually fills in the hole, accumulating a list of
dependencies (references the solution depends on) as it passes them. It moves
the dependencies to before the hole by creating new holes earlier in
the proof state and inserting a news bulletin that solves the old dependency
holes with the new ones.

> solveHole' :: Name -> [(DEF, Tip)] -> (TY :>: EXP) -> ProofState EXP
> solveHole' name deps (ty :>: tm) = do
>     lev <- getDevLev
>     es <- getEntriesAbove
>     case es of
>         B0      -> goOutBelow >> cursorUp >> solveHole' name deps (ty :>: tm)
>         _ :< e  -> pass lev e
>   where
>     pass :: Int -> Entry Bwd -> ProofState EXP
>     pass lev (EDef d@(DEF defName _ _) dev _)
>       | name == defName && occursD lev defName = throwError' $
>           err "solveHole: you can't define something in terms of itself!"
>       | name == defName = do
>           cursorUp
>           news <- makeDeps deps NONEWS
>           cursorDown
>           goIn
>           putNewsBelow news
>           let (tm', _) = tellNews news tm
>               tm'' = exp (ev tm')
>           (| def (giveOutBelow tm'') |)
>       | occursD lev defName = do
>           goIn
>           solveHole' name ((d, devTip dev):deps) (ty :>: tm)
>       | otherwise = goIn >> solveHole' name deps (ty :>: tm)
>     pass lev (EParam _ s _ l)
>       | occursP lev l = throwError' $
>             err "solveHole: param" ++ err s ++ err "occurs illegally."
>       | otherwise = cursorUp >> solveHole' name deps (ty :>: tm)
>     pass lev (EModule _ _) = goIn >> solveHole' name deps (ty :>: tm)
>
>     occursD :: Int -> Name -> Bool
>     occursD lev name = occurs lev (Just name) [] (ty :>: tm)
>     occursP :: Int -> Int -> Bool
>     occursP lev l = occurs lev Nothing [l] (ty :>: tm)

>     makeDeps :: [(DEF, Tip)] -> NewsBulletin -> ProofState NewsBulletin
>     makeDeps [] news = return news
>     makeDeps ((old, Unknown ty k) : deps) news = do
>         let (ty', _) = tellNews news ty
>         makeKinded Nothing k (fst (last name) :<: ty')
>         EDef d _ _ <- getEntryAbove
>         let op = Emit (def d)
>         makeDeps deps (addGirlNews (old{defOp = op}, GoodNews) news)
>     makeDeps _ _ = throwError' $ err "makeDeps: bad reference kind! Perhaps "
>         ++ err "solveHole was called with a term containing unexpanded definitions?"

\adam{where should this live?}

< stripShared :: NEU -> ProofState REF
< stripShared n = getInScope >>= stripShared' n
<   where
<     stripShared' :: NEU -> Entries -> ProofState REF
<     stripShared' (P ref@(_ := HOLE Hoping :<: _)) B0 = return ref
<     stripShared' (n :$ A (NP r)) (es :< EPARAM paramRef _ _ _ _)
<         | r == paramRef                      = stripShared' n es
<     stripShared' n (es :< EDEF _ _ _ _ _ _)  = stripShared' n es
<     stripShared' n (es :< EModule _ _)       = stripShared' n es
<     stripShared' n es = do
<       -- |proofTrace $ "stripShared: fail on " ++ show n|
<       throwError' $ err "stripShared: fail on" ++ errVal (N n)

What fresh hell is this:

> occurs :: Int -> Maybe Name -> [Int] -> (TY :>: EXP) -> Bool 
> occurs l n p (ty :>: tm) = 
>   let tm' = etaQuote l (ty :>: tm)
>   in occurs' n p [] tm'


> occurs' :: Maybe Name -> [Int] -> [Fin {n}] -> Tm {p, s, n} -> Bool 
> occurs' Nothing [] [] _ = False
> occurs' n p v (L g x b) = let (p', v') = occursEnv n p v g in occurs' n p' (map Fs v') b
> occurs' n p v (LK b) = occurs' n p v b
> occurs' n p v (c :- es) = any (occurs' n p v) es
> occurs' n p v (f :$ as) = (occurs' n p v f) || any (any (occurs' n p v)) as
> occurs' n p v (D def) = any (defName def ==) n -- really?
> occurs' n p v (V i) = elem i v
> occurs' n p v (P (l , s , t)) = elem l p
> occurs' n p v (e :/ t) = let (p', v') = occursEnv n p v e in occurs' n p' v' t

> occursEnv :: Maybe Name -> [Int] -> [Fin m] -> Env {m} {n} -> ([Int] , [Fin {n}]) 
> occursEnv n p v (lenv,ienv) = let (ls,os) = occursLEnv n p v lenv in
>   ((p \\ ls) `union` os, occursIEnv n p v ienv)

> occursLEnv :: Maybe Name -> [Int] -> [Fin {n}] -> LEnv {n} -> ([Int],[Int])
> occursLEnv n p v [] = ([], [])
> occursLEnv n p v ((l, t) : lenv) = 
>    let (ls, os) = occursLEnv n p v lenv 
>    in if occurs' n p v t 
>       then (l : ls, l : os)
>       else (l : ls, os) 

> occursIEnv :: Maybe Name -> [Int] -> [Fin {m}] -> IEnv {m, n} -> [Fin {n}] 
> occursIEnv n p v INix = []
> occursIEnv n p v INil = v
> occursIEnv n p v (ienv :<<: t) | occurs' n p [] t = 
>   Fz : (map Fs (occursIEnv n p v ienv)) 
> occursIEnv n p v (ienv :<<: t) = map Fs (occursIEnv n p v ienv)
