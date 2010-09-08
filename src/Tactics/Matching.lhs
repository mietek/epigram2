\section{Matching}
\label{sec:Tactics.Matching}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Tactics.Matching where

> import Prelude hiding (any, elem)

> import Control.Applicative
> import Control.Monad
> import Data.Foldable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality
> import Evidences.PropositionalEquality

> import ProofState.Edition.ProofState

> import ProofState.Interface.ProofKit

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif


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
It expands elements of $\Pi$-types by applying them to fresh references,
which must not occur in solution values (this might otherwise happen when given
a higher-order matching problem with no solutions). The fresh references are
therefore collected in a list and |checkSafe| (defined below) is called to
ensure none of the unsafe references occur.

> matchValue :: MatchSubst -> Bwd REF -> TY :>: (VAL, VAL) ->
>                   ProofState MatchSubst
> matchValue rs zs (_ :>: (NP x, t)) | x `elemSubst` rs =
>     checkSafe zs t >> insertSubst x t rs
> matchValue rs zs (PI s t :>: (v, w)) =
>     freshRef ("expand" :<: s) $ \ sRef -> do
>         let sv = pval sRef
>         matchValue rs (zs :< sRef) (t $$ A sv :>: (v $$ A sv, w $$ A sv))
> matchValue rs zs (ty :>: (v, w)) =
>     solveEquation rs $ (ty :>: v) <-> (ty :>: w)
>   where
>     solveEquation :: MatchSubst -> VAL -> ProofState MatchSubst
>     solveEquation rs TRIVIAL      = return rs
>     solveEquation rs ABSURD       = throwError' $ err "solveEquation: absurd!"
>     solveEquation rs (AND p q)    = do
>         rs' <- solveEquation rs p
>         solveEquation rs' q
>     solveEquation rs (N (op :@ [_S, NP x, _T, t]))
>       | op == eqGreen && x `elemSubst` rs =
>             checkSafe zs t >> insertSubst x t rs
>     solveEquation rs (N (op :@ [_S, N s, _T, N t]))
>       | op == eqGreen = (| fst (matchNeutral rs zs s t) |)
>     solveEquation rs (N (op :@ [_S, s, _T, t]))
>       | op == eqGreen = do
>         guard =<< (withNSupply $ equal (SET :>: (_S, _T)))
>         guard =<< (withNSupply $ equal (_S :>: (s, t)))
>         return rs
>     solveEquation rs v = error $ "solveEquation: unmatched " ++ show v


The |matchNeutral| command matches two neutrals, and returns their type along
with the matching substitution.

> matchNeutral :: MatchSubst -> Bwd REF -> NEU -> NEU ->
>                     ProofState (MatchSubst, TY)
> matchNeutral rs zs (P x)   t     | x `elemSubst` rs  = do
>     checkSafe zs (N t)
>     rs' <- insertSubst x (N t) rs
>     return (rs', pty x)
> matchNeutral rs zs (P x)  (P y)  | x == y            = return (rs, pty x)
> matchNeutral rs zs (f :$ e) (g :$ d)                 = do
>     (rs', ty) <- matchNeutral rs zs f g
>     matchElim rs' zs ty e d
> matchNeutral rs zs (fOp :@ as) (gOp :@ bs) | fOp == gOp = do
>     ty <- pity (opTyTel fOp)
>     matchArgs rs zs ty as bs
> matchNeutral rs zs a b = throwError' $ err "matchNeutral: unmatched "
>                           ++ errVal (N a) ++ err "and" ++ errVal (N b)


The |matchElim| command matches two eliminators, given the type of the neutral
being eliminated; it returns the type of the whole elimination along with the
matching substitution.
\adam{can this handle eliminators other than application?}

> matchElim :: MatchSubst -> Bwd REF -> TY -> Elim VAL -> Elim VAL ->
>                  ProofState (MatchSubst, TY)
> matchElim rs zs (PI s t) (A a) (A b) = do
>     rs' <- matchValue rs zs (s :>: (a, b))
>     return (rs', t $$ A a)
> matchElim rs zs ty a b = throwError' $ err "matchElim: unmatched!"


The |matchArgs| command matches two lists of operator arguments, given the
telescope type, and also returns the type of the operator application.

> matchArgs :: MatchSubst -> Bwd REF -> TY -> [VAL] -> [VAL] ->
>                  ProofState (MatchSubst, TY)
> matchArgs rs zs ty [] [] = return (rs, ty)
> matchArgs rs zs (PI s t) (a:as) (b:bs) = do
>     rs' <- matchValue rs zs (s :>: (a, b))
>     matchArgs rs' zs (t $$ A a) as bs


As noted above, fresh references generated when expanding $\Pi$-types must not
occur as solutions to matching problems. The |checkSafe| function throws an
error if any of the references occur in the value.

> checkSafe :: Bwd REF -> VAL -> ProofState ()
> checkSafe zs t  | any (`elem` t) zs  = throwError' $ err "checkSafe: unsafe!"
>                 | otherwise          = return ()


For testing purposes, we define a @match@ tactic that takes a telescope of
parameters to solve for, a neutral term for which those parameters are in scope,
and another term of the same type. It prints out the resulting substitution.

> import -> CochonTacticsCode where
>     matchCTactic :: [(String, DInTmRN)] -> DExTmRN -> DInTmRN -> ProofState String
>     matchCTactic xs a b = draftModule "__match" $ do
>         rs <- traverse matchHyp xs
>         (_ :=>: av :<: ty) <- elabInfer' a
>         cursorTop
>         (_ :=>: bv) <- elaborate' (ty :>: b)
>         rs' <- matchValue (bwdList rs) B0 (ty :>: (av, bv))
>         return (show rs')
>       where
>         matchHyp :: (String, DInTmRN) -> ProofState (REF, Maybe VAL)
>         matchHyp (s, t) = do
>             tt  <- elaborate' (SET :>: t)
>             r   <- assumeParam (s :<: tt)
>             return (r, Nothing)

> import -> CochonTactics where
>   : (simpleCT 
>     "match"
>     (do
>         pars <- tokenListArgs (bracket Round $ tokenPairArgs
>                                       tokenString
>                                       (keyword KwAsc)
>                                       tokenInTm) (| () |)
>         keyword KwSemi
>         tm1 <- tokenExTm
>         keyword KwSemi
>         tm2 <- tokenInTm
>         return (B0 :< pars :< tm1 :< tm2)
>      )
>      (\ [pars, ExArg a, InArg b] ->
>          matchCTactic (argList (argPair argToStr argToIn) pars) a b)
>      "match [<para>]* ; <term> ; <term> - match parameters in first term against second."
>    )
