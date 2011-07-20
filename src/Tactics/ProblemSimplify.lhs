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
> import Evidences.Primitives
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling

> import ProofState.ProofContext
> import ProofState.GetSet
> import ProofState.Navigation
> import ProofState.Interface

> import Tactics.Elimination
> import Tactics.Unification
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
>     topWrap b $
>       la "ps"  $ \_ ->  nix x :$ (B0 :< A (V Fz :$ (B0 :< Hd)) 
>                                      :< A (V Fz :$ (B0 :< Tl)))

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

> -}

If we have a function from a proof, we call on propositional simplification to
help out. If the proposition is absurd we win, and if it simplifies into a
conjunction we abstract over each conjunct individually. If the proposition
cannot be simplified, we check to see if it is an equation with a variable on
one side, and if so, eliminate it by |substEq|. Otherwise, we just put it in
the context and carry on. Note that this assumes we are at the top level.

> simplifyGoal True (PI s t) | PRF p <- ev s = do
>     simpTrace "PI PRF"
>     let evp = ev p
>     pSimp <- runPropSimplify evp
>     simplifyProp evp t pSimp
>   where
>     elimEquation :: VAL -> EXP -> ProofState EXP 
>     elimEquation (EQ _X x _Y y) t | (P (l,_,_) :$ B0) <- ev y = do
>         sc <- getInScope
>         lev <- getDevLev
>         guard $ equal lev (SET :>: (_X, _Y))
>         guard $ occurs Nothing [l] [] t
>         simpTrace $ "elimEqSimpL"
>         q    <- lambdaParam "qe"
>         let  ety  =  (("P", ARR _X SET) ->> \ _P ->
>                      (_P (wr x)) --> (_P (wr y)))
>              ex   =  wr (def substDEF) _X x y (q :$ B0)
>         elimSimplify (ety :>: ex)
>         d <- getCurrentDefinition
>         return $ applySpine (def d) sc
>     elimEquation (EQ _Y y _X x) t | (P (l,_,_) :$ B0) <- ev y = do
>         sc <- getInScope
>         lev <- getDevLev
>         guard $ equal lev (SET :>: (_X, _Y))
>         guard $ occurs Nothing [l] [] t
>         simpTrace $ "elimEqSimpR"
>         q    <- lambdaParam "qe"
>         let  ety  =  (("P", ARR _X SET) ->> \ _P ->
>                      (_P (wr x)) --> (_P (wr y)))
>              ex   =  wr (def substDEF) _X x y (q :$ (B0 :< Sym))
>         elimSimplify (ety :>: ex)
>         d <- getCurrentDefinition
>         return $ applySpine (def d) sc
>     elimEquation _ _ = (|)
>     
>     simplifyProp :: VAL -> EXP -> Simplify -> ProofState EXP
>     simplifyProp p t CannotSimplify = 
>       elimEquation p t <|> passHypothesis t
>     simplifyProp p t (SimplyAbsurd prf) = do
>         simpTrace "Absurd"
>         r    <- lambdaParam (fortran "s" [ev t] undefined)
>         let ret = (wr (def falseElimDEF) (wr prf (r :$ B0)) (wr t (r :$ B0)))
>         give ret >> return ret

>     simplifyProp p t (SimplyTrivial prf) = do
>         simpTrace "Trivial"
>         x <- trySimplifyGoal False (t $$. prf)
>         give (LK x) >> return (LK x)

>     simplifyProp p t (Simply _Ps prfPsImpP) = do
>         simpTrace "Simply"
>         sc <- getInScope
>         let x = fortran "px" [ev t] undefined
>         make ("Pig" :<: SET)
>         goIn
>         prfsPImpPs <- traverse (\((_Pi,prfPImpPi),i) -> do
>           piParam ((x ++ show i) :<: PRF _Pi)
>           return prfPImpPi) (zip (trail _Ps) [0..])
>         tp <- giveOutBelow (t $$. prfPsImpP)
>         f <- trySimplifyGoal False (applySpine (def tp) sc)
>         h <- lambdaParam x
>         let ret = (f $$$ (fmap (\pp -> A (pp $$. (h :$ B0))) (bwdList prfsPImpPs)))
>         give ret >> return ret

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


When the goal is a proof of a proposition, and we are at the top
level, we can just invoke propositional simplification...

> simplifyGoal True (PRF p) = do
>     simpTrace "PRF top"
>     propSimplifyHere
>     getCurrentDefinitionLocal

...and if we are not at the top level, we create a subgoal.

> simplifyGoal False g@(PRF _) = do
>     simpTrace "PRF not"
>     make ("prg" :<: Evidences.Tm.exp g)
>     goIn
>     x <- simplifyGoal True g
>     goOut
>     return x


If the goal is a programming problem to produce a proof, and the
proposition is trivial, then we win. However, we cannot simplify
non-trivial propositions as the user might not want us to. Similarly,
we cannot simplify inside |LABEL| unless we know we are going to solve
the goal completely.

< simplifyGoal b (LABEL _ (PRF p)) = do
<     pSimp <- runPropSimplify p
<     case pSimp of
<         Just (SimplyTrivial prf) -> do
<             topWrap b $ LRET prf :=>: LRET (evTm prf)
<         _ -> (|)



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




