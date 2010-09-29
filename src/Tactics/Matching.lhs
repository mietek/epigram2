\section{Matching}
\label{sec:Tactics.Matching}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Tactics.Matching where

> import Prelude hiding (any, elem)

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.Foldable

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Eval
> import Evidences.Operators
> import Evidences.DefinitionalEquality
> import Evidences.PropositionalEquality
> import Evidences.TypeChecker

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

> insertSubst :: REF -> VAL -> StateT MatchSubst ProofState ()
> insertSubst x t = get >>= flip help F0
>   where
>     help :: MatchSubst -> Fwd (REF, Maybe VAL) -> StateT MatchSubst ProofState ()
>     help B0 fs = error "insertSubst: reference not found!"
>     help (rs :< (y, m)) fs | x == y = case m of
>         Nothing  -> put (rs :< (x, Just t) <>< fs)
>         Just u   -> do
>             guard =<< (lift $ withNSupply (equal (pty x :>: (t, u))))
>             put (rs :< (y, m) <>< fs)
>     help (rs :< (y, m)) fs = help rs ((y, m) :> fs)


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

\adam{This is broken, because it assumes all eliminators are injective (including
projections). If you do something too complicated, it may end up matching
references with things of the wrong type. A cheap improvement would be to check
types before calling |insertSubst|, thereby giving a sound but incomplete matching
algorithm. Really we should do proper higher-order matching.} 

> matchValue :: Bwd REF -> TY :>: (VAL, VAL) -> StateT MatchSubst ProofState ()
> matchValue zs (ty :>: (NP x, t)) = do
>     rs <- get
>     if x `elemSubst` rs
>         then  lift (checkSafe zs t) >> insertSubst x t
>         else  matchValue' zs (ty :>: (NP x, t))
> matchValue zs tvv = matchValue' zs tvv

> matchValue' :: Bwd REF -> TY :>: (VAL, VAL) -> StateT MatchSubst ProofState ()
> matchValue' zs (PI s t :>: (v, w)) = do
>     rs <- get
>     rs' <- lift $ freshRef ("expand" :<: s) $ \ sRef -> do
>         let sv = pval sRef
>         execStateT (matchValue (zs :< sRef) (t $$ A sv :>: (v $$ A sv, w $$ A sv))) rs
>     put rs'

> matchValue' zs (C cty :>: (C cs, C ct)) = case halfZip cs ct of
>     Nothing   -> throwError' $ err "matchValue: unmatched constructors!"
>     Just cst  -> do
>         (mapStateT $ mapStateT $ liftError'
>             (\ v -> convertErrorVALs (fmap fst v)))
>             (canTy (chevMatchValue zs) (cty :>: cst))
>         return ()

> matchValue' zs (_ :>: (N s, N t)) = matchNeutral zs s t >> return ()

> matchValue' zs tvv = guard =<< (lift $ withNSupply $ equal tvv)


> chevMatchValue :: Bwd REF -> TY :>: (VAL, VAL) ->
>     StateT MatchSubst (ProofStateT (VAL, VAL)) (() :=>: VAL)
> chevMatchValue zs tvv@(_ :>: (v, _)) = do
>     (mapStateT $ mapStateT $ liftError' (error "matchValue: unconvertable error!"))
>         $ matchValue zs tvv
>     return (() :=>: v)


The |matchNeutral| command matches two neutrals, and returns their type along
with the matching substitution.

> matchNeutral :: Bwd REF -> NEU -> NEU -> StateT MatchSubst ProofState TY
> matchNeutral zs (P x) t = do
>     rs <- get
>     if x `elemSubst` rs
>         then do
>             lift $ checkSafe zs (N t)
>             insertSubst x (N t)
>             return (pty x)
>         else matchNeutral' zs (P x) t
> matchNeutral zs a b = matchNeutral' zs a b

> matchNeutral' :: Bwd REF -> NEU -> NEU -> StateT MatchSubst ProofState TY
> matchNeutral' zs (P x)  (P y)  | x == y            = return (pty x)
> matchNeutral' zs (f :$ e) (g :$ d)                 = do
>     C ty <- matchNeutral zs f g
>     case halfZip e d of
>         Nothing  -> throwError' $ err "matchNeutral: unmatched eliminators!"
>         Just ed  -> do
>             (_, ty') <- (mapStateT $ mapStateT $ liftError' (error "matchNeutral: unconvertable error!")) $ elimTy (chevMatchValue zs) (N f :<: ty) ed
>             return ty'
> matchNeutral' zs (fOp :@ as) (gOp :@ bs) | fOp == gOp = do
>     (_, ty) <- (mapStateT $ mapStateT $ liftError' (error "matchNeutral: unconvertable error!")) $ opTy fOp (chevMatchValue zs) (zip as bs)
>     return ty
> matchNeutral' zs a b = throwError' $ err "matchNeutral: unmatched "
>                           ++ errVal (N a) ++ err "and" ++ errVal (N b)


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
>         rs' <- runStateT (matchValue B0 (ty :>: (av, bv))) (bwdList rs)
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
