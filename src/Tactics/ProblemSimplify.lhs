%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances,
>              PatternGuards, TupleSections #-}

> module Tactics.ProblemSimplify where

> import Prelude hiding (any, foldl, elem)

> import Control.Applicative 
> import Control.Monad.Reader

> import Data.Foldable
> import Data.Traversable

> import Kit.NatFinVec
> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Kit.Trace

> import Evidences.Tm
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet
> import ProofState.Edition.Navigation
> import ProofState.Edition.Scope

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Definition
> import ProofState.Interface.Parameter
> import ProofState.Interface.Solving
> import ProofState.Interface.Lifting

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

> problemSimplify :: ProofState EXP
> problemSimplify = do
>     simpTrace "problemSimplify"
>     getHoleGoal >>= simplifyGoal True . ev

We say simplification is \emph{at the top level} if we are simplifying exactly
the current goal in the proof state. If this is not the case, we can still
make some simplifications but others require us to quote the type being
simplified and make a new goal so we are back at the top level.
The |Bool| parameter to the following functions indicates whether simplification
is at the top level.

When simplifying at the top level, we should |give| the simplified form once we
have computed it. The |topWrap| command makes this easy.

> topWrap :: Bool -> EXP -> ProofState EXP
> topWrap True   tt = give tt >> return tt
> topWrap False  tt = return tt


Once we have simplified the goal slightly, we use |trySimplifyGoal| to attempt
to continue, but give back the current result if no more simplification is
possible. If not at the top level, this has to create a new goal.

> trySimplifyGoal :: Bool -> EXP -> ProofState EXP
> trySimplifyGoal True   g = simplifyGoal True (ev g) <|>
>                                 getCurrentDefinitionLocal
> trySimplifyGoal False  g = simplifyGoal False (ev g) <|> (do
>     es  <- getEntriesAbove
>     cursorAboveLambdas
>     make ("tsg" :<: liftType es g)
>     goIn
>     let rs = params' es
>     traverse (lambdaParam . (\(_,s,_) -> s)) rs
>     d <- getCurrentDefinition
>     goOut
>     ps <- getParamsInScope
>     elimTrace "Blah"
>     return $ def d $$$. bwdList ps
>   )


We implement the simplification steps in |simplifyGoal|. This takes a boolean
parameter indicating whether simplification is at the top level, and a type
being simplified. It will return a term and value of that type (which might be
the current hole).

> simplifyGoal :: Bool -> VAL -> ProofState EXP


Functions from the unit type are simply constants, so we simplify them as such.

> simplifyGoal b (PI s t) | ONE <- ev s = do
>     simpTrace "PI ONE"
>     x <- trySimplifyGoal False (t $$ A ZERO)
>     topWrap b $ LK x


Given a function from a $\Sigma$-type, we can split it into its components.
\adam{we should not automatically split if this parameter belongs to the user
(i.e. appears in a programming problem).}

> simplifyGoal b (PI s t) | SIGMA d r <- ev s = do
>     simpTrace "PI SIGMA"
>     make ("t" :<: ARR s SET)
>     goIn
>     h <- lambdaParam (fortran "s" [ev r] undefined)
>     dd <- giveOutBelow (Evidences.Tm.exp $ ev t $$. toBody h)
>     es <- getParamsInScope
>     let  e = def dd $$$. bwdList es
>          mt =  (("d", d) ->> \a ->
>                 ("r", wr r a) ->> \b ->   
>                 wr e (PAIR a b))
>     x <- simplifyGoal False mt
>     return ZERO
>     let jd :: EXP ; jd = la "ps"  $ \_ ->  nix x :$ (B0 :< A (V Fz :$ (B0 :< Hd)) :< A (V Fz :$ (B0 :< Tl)))
>     elimTrace $ show jd
>     topWrap b  jd

> {-

Similarly, if we have a function from an enumeration, we can split it into its
branches. \adam{we should not do this automatically at all, but we need to
modify the induction principles generated for data types first.
For the moment, we check the enumeration is completely canonical, thereby
avoiding the worst problems with this simplification step.}

> simplifyGoal b (PI (ENUMT e) t) | checkTags e = do
>     simpTrace "PI ENUMT"
>     x :=>: xv <- trySimplifyGoal False (branchesOp @@ [e, t])
>     e' <- bquoteHere e
>     t' <- bquoteHere t
>     let body = N (switchOp :@ [e', NV 0, t', x])
>     topWrap b $ L ("pe" :. body) :=>: L ("pe" :. body)            
>   where
>     checkTags :: VAL -> Bool
>     checkTags NILE         = True
>     checkTags (CONSE _ e)  = checkTags e
>     checkTags _            = False

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
>         guard $ y `elem` t'
>         simpTrace $ "elimSimp: " ++ show yn
>         q    <- lambdaParam "qe"
>         _X'  <- bquoteHere _X
>         x'   <- bquoteHere x
>         let  ety  =  PI (ARR _X SET) $ L $ "P" :. [._P.
>                          ARR (N (V _P :$ A x')) (N (V _P :$ A (NP y)))
>                      ]
>              ex   =  P substEq :$ A _X' :$ A x' :$ A (NP y) :$ A (NP q)
>         elimSimplify (ety :>: ex)
>         neutralise =<< getCurrentDefinition
>     elimEquation (EQBLUE (_Y :>: NP y@(yn := DECL :<: _)) (_X :>: x)) t = do
>         guard =<< (withNSupply $ equal (SET :>: (_X, _Y)))
>         t' <- bquoteHere t
>         guard $ y `elem` t'
>         simpTrace $ "elimSimp: " ++ show yn
>         q    <- lambdaParam "qe"
>         _X'  <- bquoteHere _X
>         x'   <- bquoteHere x
>         let  ety  =  PI (ARR _X SET) $ L $ "P" :. [._P.
>                          ARR (N (V _P :$ A x')) (N (V _P :$ A (NP y)))
>                      ]
>              ex   =  P substEq :$ A _X' :$ A x' :$ A (NP y) :$ A
>                          (N (P symEq :$ A _X' :$ A (NP y) :$ A x' :$ A (NP q)))
>         elimSimplify (ety :>: ex)
>         neutralise =<< getCurrentDefinition
>     elimEquation _ _ = (|)
>     
>     simplifyProp :: VAL -> VAL -> Simplify -> ProofState (INTM :=>: VAL)
>     simplifyProp p t (SimplyAbsurd prf) = do
>         r    <- lambdaParam (fortran t)
>         t'   <- bquoteHere t
>         t''  <- annotate t' (ARR (PRF p) SET)
>         neutralise =<< give (N (nEOp :@ [prf (P r), N (t'' :$ A (NP r))]))
>     simplifyProp p t (SimplyTrivial prf) = do
>         x :=>: xv <- trySimplifyGoal False (t $$ A (evTm prf))
>         neutralise =<< give (LK x)
>
>     simplifyProp p t (SimplyOne (qr :<: qst) g h) = do
>         t'   <- bquoteHere t
>         t''  <- annotate t' (ARR (PRF p) SET)
>         let q = PIV (fortran t) qst (N (t'' :$ A ((B0 :< qr) -|| h)))
>         x :=>: xv <- trySimplifyGoal False (evTm q)
>         let y = x ?? q
>         r <- lambdaParam (fortran t)
>         neutralise =<< give (N (y :$ A (g (P r))))
>
>     simplifyProp p t (Simply qs gs h) = do
>         t'   <- bquoteHere t
>         t''  <- annotate t' (ARR (PRF p) SET)
>         let q = dischargePi qs (N (t'' :$ A h))
>         x :=>: xv <- trySimplifyGoal False (evTm q)
>         let y = x ?? q
>         r <- lambdaParam (fortran t)
>         let gs' = fmap ($ (P r)) gs
>         neutralise =<< give (N (y $## gs'))

> -}

Otherwise, we simplify $\Pi$-types by introducing a hypothesis, provided we are
at the top level.

> simplifyGoal True (PI s t) = do
>     simpTrace "PI top"
>     passHypothesis t

To simplify a $\Pi$-type when not at the top level, we have to create a subgoal.

> simplifyGoal False g@(PI s t) = do
>     simpTrace "PI not"
>     es <- getEntriesAbove
>     cursorAboveLambdas
>     make ("pig" :<: liftType es (PI s t))
>     goIn
>     let rs = params' es
>     traverse (lambdaParam . (\(_,s,_) -> s)) rs
>     simplifyGoal True g 
>     x <- getCurrentDefinition
>     goOut
>     ps <- getParamsInScope
>     return (def x $$$. bwdList ps)

> {-

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
>             topWrap b $ LRET prf :=>: LRET (evTm prf)
>         _ -> (|)

> -}

If the goal is a $\Sigma$-type, we might as well split it into its components.

> simplifyGoal b (SIGMA s t) = do
>     simpTrace "SIGMA"
>     st <- trySimplifyGoal False s
>     tt <- trySimplifyGoal False (t $$. st)
>     topWrap b $ PAIR st tt

If we are really lucky, the goal is trivial and we win.

> simplifyGoal b ONE                     = topWrap b $ ZERO 

< simplifyGoal b (LABEL _ UNIT)           = topWrap b $ LRET VOID :=>: LRET VOID


Otherwise, we cannot simplify the problem.

> simplifyGoal _ _ = throwError' $ err "simplifyGoal: cannot simplify"


When at the top level and simplifying a $\Pi$-type, |passHypothesis| introduces
a hypothesis into the context and continues simplifying. Its argument is the
codomain function of the $\Pi$-type.

> passHypothesis :: EXP -> ProofState EXP                     
> passHypothesis t = do
>     ref <- lambdaParam (fortran "x" [ev t] undefined)
>     trySimplifyGoal True (t $$. toBody ref)



The |elimSimplify| command invokes elimination with a motive, simplifies the
methods, then returns to the original goal.

> elimSimplify :: (TY :>: EXP) -> ProofState ()
> elimSimplify tt = do
>     methods <- elim tt
>     simpTrace "Eliminated!"
>     toFirstMethod
>     replicateM_ (length methods) (optional problemSimplify >> goDown)
>     goOut



> cursorAboveLambdas :: ProofState ()
> cursorAboveLambdas = do
>     es <- getEntriesAbove
>     case params es of
>         []  -> return ()
>         _   -> cursorUp >> cursorAboveLambdas




