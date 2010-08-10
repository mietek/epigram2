%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances,
>              PatternGuards, TupleSections #-}

> module Tactics.ProblemSimplify where

> import Prelude hiding (any, foldl)

> import Control.Applicative 
> import Control.Monad.Reader

> import Data.Foldable
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Lifting
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving

> import Tactics.Elimination
> import Tactics.PropositionSimplify

%endif

\section{Problem Simplification}

Now that we have considered how to simplify propositions, we wish to use this
technology to simplify programming problems. Suppose we have a goal of type
$\Delta \rightarrow T$, where $\Delta$ is some telescope of hypotheses.
There are various things we can do to simplify the problem:
\begin{itemize}
\item Split up $\Sigma$-types into their components.
\item Simplify propositions in the hypotheses and goal.
\item Solve the problem completely if it depends on a proof of false.
\item Discard uninformative hypotheses and solve trivial goals
      (of type unit or proof of trivial, for example).
\end{itemize}

The |problemSimplify| command performs these simplifications. It works by
repeatedly transforming the proof state into a simpler version, one step
at a time. It will fail if no simplification is possible. The real work is done
in |simplifyGoal| below.

> problemSimplify :: ProofState (EXTM :=>: VAL)
> problemSimplify = do
>     simpTrace "problemSimplify"
>     getHoleGoal >>= simplifyGoal True . valueOf >> getCurrentDefinition


> trySimplifyGoal :: Bool -> TY -> ProofState (INTM :=>: VAL)
> trySimplifyGoal True   ty = simplifyGoal True ty <|>
>                                 (neutralise =<< getCurrentDefinition)
> trySimplifyGoal False  ty = simplifyGoal False ty <|> (do
>                                 ty' <- bquoteHere ty
>                                 neutralise =<< make ("tsg" :<: ty'))

> annotate :: INTM -> TY -> ProofState EXTM
> annotate (N n)  _   = return n
> annotate t      ty  = bquoteHere ty >>= return . (t :?)


> topWrap :: Bool -> INTM :=>: VAL -> ProofState (INTM :=>: VAL)
> topWrap True   tt = give (termOf tt) >> return tt
> topWrap False  tt = return tt


> simplifyGoal :: Bool -> TY -> ProofState (INTM :=>: VAL)

> simplifyGoal b (PI UNIT t) = do
>     simpTrace "PI UNIT"
>     x :=>: xv <- trySimplifyGoal False (t $$ A VOID)
>     topWrap b $ LK x :=>: LK xv

> simplifyGoal b (PI (SIGMA d r) t) = do
>     simpTrace "PI SIGMA"
>     let mt =  PI d . L $ (fortran r) :. [.a. 
>               PI (r -$ [NV a]) . L $ (fortran t) :. [.b. 
>               t -$ [PAIR (NV a) (NV b)] ] ]
>     x :=>: xv <- simplifyGoal False mt
>     ex <- annotate x mt
>     let body = N (ex :$ A (N (V 0 :$ Fst)) :$ A (N (V 0 :$ Snd)))
>     topWrap b $ L ("ps" :. body) :=>: L ("ps" :. body)

> simplifyGoal b (PI (ENUMT e) t) = do
>     simpTrace "PI ENUMT"
>     x :=>: xv <- trySimplifyGoal False (branchesOp @@ [e, t])
>     e' <- bquoteHere e
>     t' <- bquoteHere t
>     let body = N (switchOp :@ [e', NV 0, t', x])
>     topWrap b $ L ("pe" :. body) :=>: L ("pe" :. body)            


This monstrosity needs to be simplified and documented.

> simplifyGoal True (PI (PRF p) t) = do
>     simpTrace "PI PRF"
>     pSimp <- runPropSimplify p
>     maybe (elimEquation p t <|> passHypothesis t) (simplifyProp p t) pSimp
>   where
>     elimEquation :: VAL -> VAL -> ProofState (INTM :=>: VAL) 
>     elimEquation (EQBLUE (_X :>: x) (_Y :>: NP y@(yn := DECL :<: _))) t = do
>         guard =<< (withNSupply $ equal (SET :>: (_X, _Y)))
>         t' <- bquoteHere t
>         guard $ y `Data.Foldable.elem` t'
>         simpTrace $ "elimSimp: " ++ show yn
>         q    <- lambdaParam "qe"
>         _X'  <- bquoteHere _X
>         x'   <- bquoteHere x
>         let  ety  =  PI (ARR _X SET) $ L $ "P" :. [._P.
>                          ARR (N (V _P :$ A x')) (N (V _P :$ A (NP y)))
>                      ]
>              ex   =  P substEq :$ A _X' :$ A x' :$ A (NP y) :$ A (NP q)
>         elimSimplify (ety :>: N ex)
>         neutralise =<< getCurrentDefinition
>     elimEquation (EQBLUE (_Y :>: NP y@(yn := DECL :<: _)) (_X :>: x)) t = do
>         guard =<< (withNSupply $ equal (SET :>: (_X, _Y)))
>         t' <- bquoteHere t
>         guard $ y `Data.Foldable.elem` t'
>         simpTrace $ "elimSimp: " ++ show yn
>         q    <- lambdaParam "qe"
>         _X'  <- bquoteHere _X
>         x'   <- bquoteHere x
>         let  ety  =  PI (ARR _X SET) $ L $ "P" :. [._P.
>                          ARR (N (V _P :$ A x')) (N (V _P :$ A (NP y)))
>                      ]
>              ex   =  P substEq :$ A _X' :$ A x' :$ A (NP y) :$ A
>                          (N (P symEq :$ A _X' :$ A (NP y) :$ A x' :$ A (NP q)))
>         elimSimplify (ety :>: N ex)
>         neutralise =<< getCurrentDefinition
>     elimEquation _ _ = (|)
>     
>     simplifyProp :: VAL -> VAL -> Simplify -> ProofState (INTM :=>: VAL)
>     simplifyProp p t (SimplyAbsurd prf) = do
>         r <- lambdaParam (fortran t)
>         let pr = prf (NP r)
>         nonsense <- bquoteHere (nEOp @@ [pr, t $$ A (NP r)])
>         neutralise =<< give nonsense
>     simplifyProp p t (SimplyTrivial prf) = do
>         x :=>: xv <- trySimplifyGoal False (t $$ A prf)
>         neutralise =<< give (LK x)
>     simplifyProp p t (Simply qs gs h) = do
>         q <- dischargePiLots qs (t $$ A h)
>         x :=>: xv <- trySimplifyGoal False q
>         y <- annotate x q
>         r <- lambdaParam (fortran t)
>         gs' <- traverse (bquoteHere . ($$ A (NP r))) gs
>         neutralise =<< give (N (y $## trail gs'))

> simplifyGoal True (PI s t) = do
>     simpTrace "PI top"
>     passHypothesis t

> simplifyGoal False g@(PI _ _) = do
>     simpTrace "PI not"
>     g' <- bquoteHere g
>     make ("pig" :<: g')
>     goIn
>     simplifyGoal True g
>     x :=>: xv <- getCurrentDefinition
>     goOut
>     return $ N x :=>: xv

> simplifyGoal True (PRF p) = do
>     simpTrace "PRF top"
>     propSimplifyHere
>     getCurrentDefinition >>= neutralise

> simplifyGoal False g@(PRF _) = do
>     simpTrace "PRF not"
>     g' <- bquoteHere g
>     make ("prg" :<: g')
>     goIn
>     x :=>: xv <- simplifyGoal True g
>     goOut
>     return $ x :=>: xv

> simplifyGoal b UNIT = topWrap b $ VOID :=>: VOID

> simplifyGoal b (SIGMA s t) = do
>     simpTrace "SIGMA"
>     stm :=>: sv <- trySimplifyGoal False s
>     ttm :=>: tv <- trySimplifyGoal False (t $$ A sv)
>     topWrap b $ PAIR stm ttm :=>: PAIR sv tv

> simplifyGoal b (LABEL _ UNIT)           = topWrap b $ LRET VOID :=>: LRET VOID
> simplifyGoal b (LABEL _ (PRF TRIVIAL))  = topWrap b $ LRET VOID :=>: LRET VOID

> simplifyGoal _ _ = throwError' $ err "simplifyGoal: cannot simplify"



> passHypothesis :: VAL -> ProofState (INTM :=>: VAL)                     
> passHypothesis t = do
>     ref <- lambdaParam (fortran t)
>     trySimplifyGoal True (t $$ A (NP ref))

The |elimSimplify| command invokes elimination with a motive, simplifies the
methods, then returns to the original goal.

> elimSimplify :: (TY :>: INTM) -> ProofState ()
> elimSimplify tt = do
>     elim Nothing tt
>     simpTrace "Eliminated!"
>     toFirstMethod
>     optional problemSimplify            -- simplify first method
>     many (goDown >> problemSimplify)    -- simplify other methods
>     goOut                               -- out to makeE
>     goOut                               -- out to original goal



> import -> CochonTactics where
>   : nullaryCT "simplify" (problemSimplify >> optional seekGoal >> return "Simplified.")
>       "simplify - simplifies the current problem."