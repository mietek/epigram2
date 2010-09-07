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
\label{subsec:Elaboration.Unification.Matching}

A \emph{matching substitution} is a list of references with their values, if any.

> type MatchSubst = Bwd (REF, Maybe VAL)

It is easy to decide if a reference is an element of such a substitution:

> elemSubst :: REF -> MatchSubst -> Bool
> elemSubst r = any ((r ==) . fst)

When inserting a new reference-value pair into the substitution, we ensure that
it is consistent with any value already given to the reference.

> insertSubst :: REF -> VAL -> MatchSubst -> ProofState MatchSubst
> insertSubst x t B0 = error "insertSubst: reference not found!"
> insertSubst x t (rs :< (y, m)) | x == y = case m of
>     Nothing  -> return (rs :< (x, Just t))
>     Just u   -> do
>         guard =<< withNSupply (equal (pty x :>: (t, u)))
>         return (rs :< (y, m))
> insertSubst x t (rs :< (y, m)) = (| (insertSubst x t rs) :< ~(y, m) |)


The matching commands, defined below, take a matching substitution (initially
with no values for the references) and a pair of objects. The references must
only exist in the first object, and each reference may only depend on those
before it (in the usual telescopic style). Each command will produce an updated
substitution, potentially with more references defined.

Note that the resulting values may contain earlier references that need to be
substituted out. Any references left with no value at the end are unconstrained
by the matching problem.

The |matchValue| command requires the type of the values to be pushed in.
\adam{can we be sure the references used to expand pi-types will not appear
in the final output?}

> matchValue :: MatchSubst -> TY :>: (VAL, VAL) -> ProofState MatchSubst
> matchValue rs (_ :>: (NP x, t)) | x `elemSubst` rs = insertSubst x t rs
> matchValue rs (PI s t :>: (v, w)) =
>     freshRef ("expand" :<: s) $ \ sRef -> do
>         let sv = pval sRef
>         matchValue rs (t $$ A sv :>: (v $$ A sv, w $$ A sv))
> matchValue rs (ty :>: (v, w)) =
>     solveEquation rs $ (ty :>: v) <-> (ty :>: w)
>   where
>     solveEquation :: MatchSubst -> VAL -> ProofState MatchSubst
>     solveEquation rs TRIVIAL      = return rs
>     solveEquation rs ABSURD       = throwError' $ err "solveEquation: absurd!"
>     solveEquation rs (AND p q)    = do
>         rs' <- solveEquation rs p
>         solveEquation rs' q
>     solveEquation rs (N (op :@ [_S, NP x, _T, t]))
>       | op == eqGreen && x `elemSubst` rs = insertSubst x t rs
>     solveEquation rs (N (op :@ [_S, N s, _T, N t]))
>       | op == eqGreen = (| fst (matchNeutral rs s t) |)
>     solveEquation rs (N (op :@ [_S, s, _T, t]))
>       | op == eqGreen = do
>         guard =<< (withNSupply $ equal (SET :>: (_S, _T)))
>         guard =<< (withNSupply $ equal (_S :>: (s, t)))
>         return rs
>     solveEquation rs v = error $ "solveEquation: unmatched " ++ show v


The |matchNeutral| command generates the type of the values as well as the
matching substitution.

> matchNeutral :: MatchSubst-> NEU -> NEU -> ProofState (MatchSubst, TY)
> matchNeutral rs (P x)   t     | x `elemSubst` rs  = do
>     rs' <- insertSubst x (N t) rs
>     return (rs', pty x)
> matchNeutral rs (P x)  (P y)  | x == y       = return (rs, pty x)
> matchNeutral rs (f :$ e) (g :$ d)            = do
>     (rs', ty) <- matchNeutral rs f g
>     matchElim rs' ty e d
> matchNeutral rs a b = throwError' $ err "matchNeutral: unmatched "
>                           ++ errVal (N a) ++ err "and" ++ errVal (N b)


The |matchElim| command requires the type of the neutral being eliminated, and
produces the type of the whole elimination.

> matchElim :: MatchSubst -> TY -> Elim VAL -> Elim VAL ->
>                  ProofState (MatchSubst, TY)
> matchElim rs (PI s t) (A a) (A b) = do
>     rs' <- matchValue rs (s :>: (a, b))
>     return (rs', t $$ A a)
> matchElim rs ty a b = throwError' $ err "matchElim: unmatched!"





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
