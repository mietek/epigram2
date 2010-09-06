\section{Unification and matching}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Elaboration.Unification where

> import Prelude hiding (any, elem)

> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import qualified Data.Monoid as M

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality
> import Evidences.PropositionalEquality

> import ProofState.Structure.Developments

> import ProofState.Edition.News
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import ProofState.Interface.Search
> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace

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


\subsection{Matching}


\pierre{|matchLabels| and |matchParams| comes from Elaboration. Note
that |matchLabels| is abused in a nasty way. This is a temporary
fix. Note also that we removed the check that |sn| and |tn| are
|Fake|. Go to hell if you're unhappy.}

> matchLabels :: NEU -> NEU -> [(VAL, VAL)] -> Maybe (REF, [(VAL, VAL)])
> matchLabels (P ref@(sn := _ :<: _)) (P (tn := _ :<: _)) ps
>     | sn == tn   = Just (ref, ps)
>     | otherwise  = Nothing
> matchLabels (s :$ A as) (t :$ A at) ps = matchLabels s t ((as, at):ps)
> matchLabels _ _ _ = Nothing 


> matchParams :: Bwd REF -> TY -> [(VAL, VAL)] -> [(REF, VAL)] -> ProofState [(REF, VAL)]
> matchParams rs ty        []               subst = return subst
> matchParams rs (PI s t)  ((as, at) : ps)  subst = do
>     subst' <- matchValues rs (s :>: (as, at))
>     matchParams rs (t $$ A as) ps (subst ++ subst')


The |matchValues| command takes a pair of values of the same type, and attempts
to match the hoping holes of the first value to parts of the second value.

> matchValues :: Bwd REF -> TY :>: (VAL, VAL) -> ProofState [(REF, VAL)]
> matchValues rs (_ :>: (NP x, t)) | x `elem` rs = return [(x, t)]
> matchValues rs (PI s t :>: (v, w)) = freshRef (fortran t :<: s) $ \ sRef -> do
>     let sv = pval sRef
>     matchValues rs (t $$ A sv :>: (v $$ A sv, w $$ A sv))
> matchValues rs (ty :>: (v, w)) = solveEquation $ (ty :>: v) <-> (ty :>: w)
>   where
>     solveEquation :: VAL -> ProofState [(REF, VAL)]
>     solveEquation TRIVIAL      = return []
>     solveEquation ABSURD       = throwError' $ err "solveEquation: absurd!"
>     solveEquation (AND p q)    = (| (solveEquation p) ++ (solveEquation q) |)
>     solveEquation (N (op :@ [_S, N s, _T, N t])) 
>         | op == eqGreen ,
>           Just (ref, args) <- matchLabels s t [] = 
>       matchParams rs (pty ref) args []
>     solveEquation (N (op :@ [_S, NP ref, _T, t]))
>       | op == eqGreen && ref `elem` rs = return [(ref, t)]
>     solveEquation (N (op :@ [_S, N s, _T, N t]))
>       | op == eqGreen = (| fst (matchNeutral rs s t) |)
>     solveEquation (N (op :@ [_S, s, _T, t]))
>       | op == eqGreen = do
>         guard =<< (withNSupply $ equal (SET :>: (_S, _T)))
>         guard =<< (withNSupply $ equal (_S :>: (s, t)))
>         return []
>     solveEquation v = error $ "solveEquation: unmatched " ++ show v


> matchNeutral :: Bwd REF -> NEU -> NEU -> ProofState ([(REF, VAL)], TY)
> matchNeutral rs (P x)   t     | x `elem` rs  = return ([(x, N t)], pty x)
> matchNeutral rs (P x)  (P y)  | x == y       = return ([], pty x)
> matchNeutral rs (f :$ e) (g :$ d)            = do
>     (ss, ty)    <- matchNeutral rs f g
>     (ss', ty')  <- matchElim rs ty e d
>     return (ss ++ ss', ty')
> matchNeutral rs (fOp :@ as) (gOp :@ bs) | fOp == gOp =
>     undefined -- matchParams rs (pity (opTyTel fOp)) (zip as bs) []
> matchNeutral rs a b = throwError' $ err "matchNeutral: unmatched "
>                           ++ errVal (N a) ++ err "and" ++ errVal (N b)

> matchElim :: Bwd REF -> TY -> Elim VAL -> Elim VAL -> ProofState ([(REF, VAL)], TY)
> matchElim rs (PI s t) (A a) (A b) = do
>     ss <- matchValues rs (s :>: (a, b))
>     return (ss, t $$ A a)
> matchElim rs ty a b = throwError' $ err "matchElim: unmatched!"


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
