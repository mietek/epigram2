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
There are various things we can do to simplify the problem, such as:
\begin{itemize}
\item splitting up $\Sigma$-types into their components;
\item simplifying propositions in the hypotheses and goal;
\item discarding uninformative hypotheses; and
\item solving the problem completely if it is trivial (for example, if it
      depends on a proof of false).
\end{itemize}

The |problemSimplify| command performs these simplifications. It works by
repeatedly transforming the proof state into a simpler version, one step
at a time. It will fail if no simplification is possible. The real work is done
in |simplifyGoal| below.

> problemSimplify :: ProofState (EXTM :=>: VAL)
> problemSimplify = do
>     simpTrace "problemSimplify"
>     getHoleGoal >>= simplifyGoal True . valueOf >> getCurrentDefinition

We say simplification is \emph{at the top level} if we are simplifying exactly
the current goal in the proof state. If this is not the case, we can still
make some simplifications but others require us to quote the type being
simplified and make a new goal so we are back at the top level.
The |Bool| parameter to the following functions indicates whether simplification
is at the top level.

When simplifying at the top level, we should |give| the simplified form once we
have computed it. The |topWrap| command makes this easy.

> topWrap :: Bool -> INTM :=>: VAL -> ProofState (INTM :=>: VAL)
> topWrap True   tt = give (termOf tt) >> return tt
> topWrap False  tt = return tt

Once we have simplified the goal slightly, we use |trySimplifyGoal| to attempt
to continue, but give back the current result if no more simplification is
possible. If not at the top level, this has to create a new goal.

> trySimplifyGoal :: Bool -> TY -> ProofState (INTM :=>: VAL)
> trySimplifyGoal True   ty = simplifyGoal True ty <|>
>                                 (neutralise =<< getCurrentDefinition)
> trySimplifyGoal False  ty = simplifyGoal False ty <|> (do
>                                 ty' <- bquoteHere ty
>                                 neutralise =<< make ("tsg" :<: ty'))

We implement the simplification steps in |simplifyGoal|. This takes a boolean
parameter indicating whether simplification is at the top level, and a type
being simplified. It will return a term and value of that type (which might be
the current hole).

> simplifyGoal :: Bool -> TY -> ProofState (INTM :=>: VAL)

Functions from the unit type are simply constants, so we simplify them as such.

> simplifyGoal b (PI UNIT t) = do
>     simpTrace "PI UNIT"
>     x :=>: xv <- trySimplifyGoal False (t $$ A VOID)
>     topWrap b $ LK x :=>: LK xv

Given a function from a $\Sigma$-type, we can split it into its components.
\adam{we should not automatically split if this parameter belongs to the user
(i.e. appears in a programming problem).}

> simplifyGoal b (PI (SIGMA d r) t) = do
>     simpTrace "PI SIGMA"
>     let mt =  PI d . L $ (fortran r) :. [.a. 
>               PI (r -$ [NV a]) . L $ (fortran t) :. [.b. 
>               t -$ [PAIR (NV a) (NV b)] ] ]
>     x :=>: xv <- simplifyGoal False mt
>     ex <- annotate x mt
>     let body = N (ex :$ A (N (V 0 :$ Fst)) :$ A (N (V 0 :$ Snd)))
>     topWrap b $ L ("ps" :. body) :=>: L ("ps" :. body)

Similarly, if we have a function from an enumeration, we can split it into its
branches. \adam{we should not do this automatically at all, but we need to
modify the induction principles generated for data types first.}

> simplifyGoal b (PI (ENUMT e) t) = do
>     simpTrace "PI ENUMT"
>     x :=>: xv <- trySimplifyGoal False (branchesOp @@ [e, t])
>     e' <- bquoteHere e
>     t' <- bquoteHere t
>     let body = N (switchOp :@ [e', NV 0, t', x])
>     topWrap b $ L ("pe" :. body) :=>: L ("pe" :. body)            

If we have a function from a proof, we call on propositional simplification to
help out. If the proposition is absurd we win, and if it simplifies into a
conjunction we abstract over each conjunct individually. If the proposition
cannot be simplified, we check to see if it is an equation with a variable on
one side, and if so, eliminate it by |substEq|. Otherwise, we just put it in
the context and carry on. Note that this assumes we are at the top level.

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

Otherwise, we simplify $\Pi$-types by introducing a hypothesis, provided we are
at the top level.

> simplifyGoal True (PI s t) = do
>     simpTrace "PI top"
>     passHypothesis t

To simplify a $\Pi$-type when not at the top level, we have to create a subgoal.

> simplifyGoal False g@(PI _ _) = do
>     simpTrace "PI not"
>     g' <- bquoteHere g
>     make ("pig" :<: g')
>     goIn
>     simplifyGoal True g
>     x :=>: xv <- getCurrentDefinition
>     goOut
>     return $ N x :=>: xv

When the goal is a proof of a proposition, and we are at the top level, we can
just invoke propositional simplification...

> simplifyGoal True (PRF p) = do
>     simpTrace "PRF top"
>     propSimplifyHere
>     getCurrentDefinition >>= neutralise

...and if we are not at the top level, we create a subgoal.

> simplifyGoal False g@(PRF _) = do
>     simpTrace "PRF not"
>     g' <- bquoteHere g
>     make ("prg" :<: g')
>     goIn
>     x :=>: xv <- simplifyGoal True g
>     goOut
>     return $ x :=>: xv

If the goal is a programming problem to produce a proof, and the proposition is
trivial, then we win. However, we cannot simplify non-trivial propositions as
the user might not want us to. Similarly, we cannot simplify inside |LABEL|
unless we know we are going to solve the goal completely.

> simplifyGoal b (LABEL _ (PRF p)) = do
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Just (SimplyTrivial prf) -> do
>             prf' <- bquoteHere prf
>             topWrap b $ LRET prf' :=>: LRET prf
>         _ -> (|)

If the goal is a $\Sigma$-type, we might as well split it into its components.

> simplifyGoal b (SIGMA s t) = do
>     simpTrace "SIGMA"
>     stm :=>: sv <- trySimplifyGoal False s
>     ttm :=>: tv <- trySimplifyGoal False (t $$ A sv)
>     topWrap b $ PAIR stm ttm :=>: PAIR sv tv

If we are really lucky, the goal is trivial and we win.

> simplifyGoal b UNIT                     = topWrap b $ VOID :=>: VOID
> simplifyGoal b (LABEL _ UNIT)           = topWrap b $ LRET VOID :=>: LRET VOID

Otherwise, we cannot simplify the problem.

> simplifyGoal _ _ = throwError' $ err "simplifyGoal: cannot simplify"


When at the top level and simplifying a $\Pi$-type, |passHypothesis| introduces
a hypothesis into the context and continues simplifying. Its argument is the
codomain function of the $\Pi$-type.

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