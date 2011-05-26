\section{Matching}
\label{sec:Tactics.Matching}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards, FlexibleContexts #-}

> module Tactics.Matching where

> import Prelude hiding (any, elem, exp)

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Error
> import Data.Foldable
> import Data.Maybe

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.TypeChecker
> import Evidences.TypeCheckRules
> import Evidences.ErrorHandling

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.ProofKit

> import Kit.BwdFwd
> import Kit.MissingLibrary

%endif

A \emph{matching substitution} is a list of references with their values, if any.

> type MatchSubst = Bwd ((Int, String, TY), Maybe EXP)

It is easy to decide if a reference is an element of such a substitution:

> elemSubst :: (Int, String, TY) -> MatchSubst -> Bool
> elemSubst (l,_,_) = any ((\(l',_,_) -> l == l') . fst)

When inserting a new reference-value pair into the substitution, we ensure that
it is consistent with any value already given to the reference.

> insertSubst :: (Applicative m, MonadError StackError m) => 
>                Int -> (Int, String, TY) -> EXP -> StateT MatchSubst m ()
> insertSubst lev a@(l,x,ty) t = get >>= flip help F0
>   where
>     help :: (Applicative m, MonadError StackError m) => 
>             MatchSubst -> Fwd ((Int, String, TY), Maybe EXP) -> StateT MatchSubst m ()
>     help B0 fs = error "insertSubst: reference not found!"
>     help (rs :< (b@(l',x',ty'), m)) fs | l == l' = case m of
>         Nothing  -> put (rs :< (a, Just t) <>< fs)
>         Just u   -> if (equal lev (ty :>: (t, u))) 
>                     then put (rs :< (b, m) <>< fs)
>                     else throwError' $ err "Multiple Solutions to matching problem"
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

> matchValue :: (Applicative m, MonadError StackError m) => 
>               Int -> Bwd (Int, String, TY) -> TY :>: (VAL, VAL) -> StateT MatchSubst m ()
> matchValue lev zs (ty :>: (P x :$ B0, t)) = do
>     rs <- get
>     if x `elemSubst` rs
>         then  lift (checkSafe zs t) >> insertSubst lev x (exp t)
>         else  matchValue' lev zs (ev ty :>: (P x :$ B0, t))
> matchValue lev zs (ty :>: vv) = matchValue' lev zs (ev ty :>: vv)



> matchValue' :: (Applicative m, MonadError StackError m) => 
>                Int -> Bwd (Int, String, TY) -> VAL :>: (VAL, VAL) -> StateT MatchSubst m ()

> matchValue' lev zs (PI s t :>: (v, w)) = do
>     rs <- get
>     rs' <- lift $ do
>         let lxty = (lev, "expand", s)
>         let p = P lxty :$ B0
>         execStateT (matchValue (lev+1) (zs :< lxty) (t $$ A p :>: (v $$ A p, w $$ A p))) rs
>     put rs'

> matchValue' lev zs (cty :- asty :>: (cs :- ass, ct :- tas)) | cs == ct = 
>   matchCan lev zs (fromJust (canTy ((cty, asty) :>: cs)) :>: (ass, tas))

> matchValue' lev zs (cty :- asty :>: (cs :- ass, ct :- tas)) = 
>     throwError' $ err "matchValue: unmatched constructors!"

> matchValue' lev zs (_ :>: (s@(D def ss op), t@(D def' ss' op'))) = 
>   matchNeutral lev zs s t >> return ()

> matchValue' lev zs (_ :>: (s@(_ :$ _), t@(_ :$ _))) = matchNeutral lev zs s t >> return ()

> matchValue' lev zs (ty :>: (v, w)) | (equal lev (exp ty :>: (exp v, exp w))) = return ()

> matchValue' _ _ _ = throwError' $ err "matchValue' flail"


> matchCan :: (Applicative m, MonadError StackError m) => 
>             Int -> Bwd (Int, String, TY) -> VAL :>: ([EXP], [EXP]) -> StateT MatchSubst m ()
> matchCan lev zs (ONE :>: ([],[])) = return ()
> matchCan lev zs (SIGMA s t :>: (a : as, b : bs)) = do
>   let bv = ev b
>   matchValue lev zs (s :>: (ev a, bv))
>   matchCan lev zs (ev t $$. bv :>: (as, bs))

The |matchNeutral| command matches two neutrals, and returns their type along
with the matching substitution.

> matchNeutral :: (Applicative m, MonadError StackError m) => 
>                 Int -> Bwd (Int, String, TY) -> VAL -> VAL -> StateT MatchSubst m TY
> matchNeutral = undefined

> {-

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

> -}

As noted above, fresh references generated when expanding $\Pi$-types must not
occur as solutions to matching problems. The |checkSafe| function throws an
error if any of the references occur in the value.

> checkSafe :: (Applicative m, MonadError StackError m) => 
>              Bwd (Int, String, TY) -> VAL -> m ()
> checkSafe = undefined


> {-
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

> -}
