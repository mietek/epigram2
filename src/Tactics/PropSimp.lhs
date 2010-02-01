%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances #-}

> module Tactics.PropSimp where

> import Debug.Trace

> import Control.Applicative 
> import Control.Monad.Reader hiding (mapM)
> import Data.Foldable
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import DisplayLang.PrettyPrint

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.ProofState
> import ProofState.ProofKit

> import Tactics.Information

> import Prelude hiding (any, foldl, mapM)

%endif

\section{Propositional Simplification}

\subsection{Setting the Scene}

\question{What should the terminology be?}

A \emph{normal} proposition is either |FF| or a conjunction of \emph{q-neutral}
propositions. A q-neutral context is a context all of whose propositions are q-neutral.
A \emph{q-neutral} proposition is either:
\begin{itemize}
\item a neutral term of type |Prop|;
\item a blue equation with (at least) one neutral side;
\item |(x : S) => P|, with |S| not a proof and |P| q-neutral; or
\item |(x :- P) => Q|, with |P| and |Q| q-neutral and |P| not |FF|.
\end{itemize}


Given $\Delta \vdash p$, the propositional simplifier will either 
\begin{itemize}
\item discover that $p$ is absurd and provide a proof
$\Delta \vdash f :\!\!-~ p \Rightarrow \bot$, represented by |Left f|; or
\item simplify $p$ to a conjunction $\bigwedge_i q_i$ together with proofs
$\Delta \vdash g_i :\!\!-~ p \Rightarrow q_i$ and $\Delta, \Gamma \vdash h :\!\!-~ p$,
where $\Gamma = \{q_i\}_i$, represented by |Right (qs, gs, h)|.
\end{itemize}

> type Simplify = Either (VAL -> VAL) (Bwd REF, Bwd VAL, VAL)

> pattern Simply qs gs h     = Right (qs, gs, h)
> pattern SimplyAbsurd prf   = Left prf
> pattern SimplyTrivial prf  = Simply B0 B0 prf
> pattern SimplyOne q g h    = Simply (B0 :< q) (B0 :< g) h


> type Simplifier x = ReaderT NameSupply Maybe x
                 

The |dischargeLots| function discharges and $\lambda$-binds a list of references over a |VAL|.

> dischargeLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeLots bs v = do
>     v' <- bquote bs v
>     return (evTm (wrapLambdas bs v'))
>   where
>     wrapLambdas :: Bwd REF -> INTM -> INTM
>     wrapLambdas B0 tm = tm
>     wrapLambdas (bs :< (n := _)) tm = wrapLambdas bs (L (fst (last n) :. tm))


The |dischargeAllLots| function discharges and $\forall$-binds a list of references over a |VAL|.
It checks to see which are actually used, and inserts constant scopes |K| where possible.

> dischargeFLots :: (NameSupplier m) => (Bool -> String -> INTM -> INTM -> INTM) -> Bwd REF -> VAL -> m VAL
> dischargeFLots f bs v = do
>     temp <- bquote B0 v
>     let cs = fmap (contains temp) bs
>     v' <- bquote bs v
>     v'' <- wrapFs bs cs v'
>     return (evTm v'')
>   where
>     wrapFs :: (NameSupplier m) => Bwd REF -> Bwd Bool -> INTM -> m INTM
>     wrapFs B0 _ tm = return tm
>     wrapFs (bs :< (n := _ :<: ty)) (cs :< c) tm = do
>         ty' <- bquote B0 ty
>         wrapFs bs cs (f c (fst (last n)) ty' tm)

>     contains :: INTM -> REF -> Bool
>     contains tm ref = any (== ref) tm


> dischargeAllLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeAllLots = dischargeFLots f
>   where 
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p (PRF q) = PRF (ALLV x p q)
>     f False  x p (PRF q) = PRF (ALL p (LK q))

> dischargePiLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargePiLots = dischargeFLots f
>   where
>     f :: Bool -> String -> INTM -> INTM -> INTM
>     f True   x p q = PIV x p q
>     f False  x p q = PI p (LK q)


The |dischargeRef| function calls |dischargeLots| on the type of a reference.

> dischargeRef :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRef bs (n := DECL :<: ty) = do
>     ty' <- dischargeLots bs ty
>     return (n := DECL :<: ty')


The |dischargeRefAlls| function calls |dischargeAllLots| on the type of a reference.

> dischargeRefAlls :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRefAlls bs (n := DECL :<: ty) = do
>     ty' <- dischargeAllLots bs ty
>     return (n := DECL :<: ty')

The |dischargeRefPis| function calls |dischargePiLots| on the type of a reference.

> dischargeRefPis :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRefPis bs (n := DECL :<: ty) = do
>     ty' <- dischargePiLots bs ty
>     return (n := DECL :<: ty')




The |magic ty| function takes a proof of |FF| and yields a value of type |ty|.

> magic :: TY -> VAL -> VAL
> magic ty no = nEOp @@ [no, ty]


The |...| operator is composition of |VAL| functions.

> (...) :: VAL -> VAL -> VAL
> f ... g = L (HF "x" (\x -> f $$ A (g $$ A x)))

The curiously more useful |..!| operator is composition of a genuine |VAL|
function with a |VAL -> VAL| function.

> (..!) :: VAL -> (VAL -> VAL) -> VAL
> f ..! g = L (HF "x" (\x -> f $$ A (g x)))


\subsection{Simplification in Action}

The |propSimplify| command takes a proposition and attempts to simplify it.

> propSimplify :: Bwd REF -> VAL -> Simplifier Simplify


Simplifying |TT| and |FF| is remarkably easy.

> propSimplify _ ABSURD   = return (SimplyAbsurd   id)
> propSimplify _ TRIVIAL  = return (SimplyTrivial  VOID)


To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify delta (AND p1 p2) = forkNSupply "psAnd1" (forceSimplify delta p1)
>     (\ p1Simp -> forkNSupply "psAnd2" (forceSimplify delta p2)
>         (\ p2Simp ->
>             return (simplifyAnd p1Simp p2Simp)))
>   where
>     simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

>     simplifyAnd (SimplyAbsurd prf) _ = SimplyAbsurd (prf . ($$ Fst))
>     simplifyAnd _ (SimplyAbsurd prf) = SimplyAbsurd (prf . ($$ Snd))
         
Otherwise, we can simplify the conjunction, post-composing the proofs with
the application of |Fst| or |Snd| as appropriate.

>     simplifyAnd (Simply q1s g1s h1) (Simply q2s g2s h2) =
>         Simply (q1s <+> q2s)
>             (fmap (..! ($$ Fst)) g1s <+> (fmap (..! ($$ Snd)) g2s))
>             (PAIR h1 h2)



To simplify |p = (x :- s) => t|, we first try to simplify |s|:

> propSimplify delta p@(ALL (PRF s) l) =
>     forkNSupply "psImp1" (forceSimplifyNamed delta s (fortran l)) antecedent
>   where
>     antecedent :: Simplify -> Simplifier Simplify

If |s| is absurd then |p| is trivial, which we can prove by doing |magic|
whenever someone gives us an element of |s|.

>     antecedent (SimplyAbsurd prfAbsurdS) = return (SimplyTrivial
>         (L (HF "antecedentAbsurd" (\sv ->
>             magic (PRF (l $$ A sv)) (prfAbsurdS sv)))))

If |s| is trivial, then we go under the binder by applying the proof, and then
simplify |t|. Then |p| simplifies to the result of simplifying |t|, with the
proofs constructed by $\lambda$-abstracting in one direction and applying the
proof of |s| in the other direction.

>     antecedent (SimplyTrivial prfS) =
>         forkNSupply "psImp2" (forceSimplify delta (l $$ A prfS)) consequentTrivial
>       where
>         consequentTrivial :: Simplify -> Simplifier Simplify
>         consequentTrivial (SimplyAbsurd prfAbsurdT) =
>             return (SimplyAbsurd (prfAbsurdT . ($$ A prfS)))
>         consequentTrivial (SimplyTrivial prfT)  = return (SimplyTrivial (LK prfT))
>         consequentTrivial (Simply tqs tgs th)   = return (Simply tqs
>             (fmap (..! ($$ A prfS)) tgs)
>             (LK th))

If |s| simplifies nontrivially, we have a bit more work to do. We simplify |t|
under the binder by adding the simplified conjuncts of |s| to the context and
applying |l| to |sh| (the proof of |s| in the extended context). 

>     antecedent (Simply sqs sgs sh) =
>         forkNSupply "psImp3" (forceSimplify (delta <+> sqs) (l $$ A sh)) consequent
>       where
>         consequent :: Simplify -> Simplifier Simplify
>         consequent (SimplyAbsurd prfAbsurdT) = do
>             madness <- dischargeAllLots sqs (PRF ABSURD)
>             freshRef ("madness" :<: madness) (\ref -> 
>                 freshRef ("pref" :<: p) (\pref -> do
>                     g <- dischargeLots sqs (prfAbsurdT (NP pref $$ A sh))
>                     g' <- discharge pref g
>                     return (SimplyOne ref
>                         (L (HF "p" (\pv -> g' $$ A pv)))
>                         (L (HF "consequentAbsurd" (\sv -> magic (PRF (l $$ A sv))
>                         (NP ref $$$ (fmap (A . ($$ A sv)) sgs))))))
>                   )
>               )

If the consequent |t| is trivial, then the implication is trivial, which we can
prove as follows:
\begin{enumerate}
\item Discharge the proof of |t| over the conjuncts |sqs| to get a $\lambda$-lifted proof |prfT'|.
\item Construct a proof of |(x :\!\!- s) => t| that takes a proof of |s| and applies the proofs
|sgs| to get proofs of the |sqs|, which can then be passed to |prfT'| to get a proof of |t|.
\end{enumerate}

>         consequent (SimplyTrivial prfT) = do
>             prfT' <- dischargeLots sqs prfT
>             return (SimplyTrivial (L (HF "consequentTrivial" (\sv ->
>                 prfT' $$$ (fmap (A . ($$ A sv)) sgs)))))

Otherwise, if the consequent simplifies, we proceed as follows.

Suppose that $\Delta \vdash s \leadsto \bigwedge_i sq_i$
with proofs $\Delta \vdash sg_i : s \Rightarrow sq_i$ and
$\Delta, \Gamma \vdash sh : s$ where $\Gamma = x_0 : sq_0, ..., x_n : sq_n$.

Suppose further that $\Delta, \Gamma \vdash t \leadsto \bigwedge_j tq_j$
with proofs $\Delta \vdash tg_j : t \Rightarrow tq_j$ and
$\Delta, \Gamma, \Xi \vdash sh : s$ where $\Xi = y_0 : tq_0, ..., y_m : tq_m$.

Let $\overline t ^ \Gamma$ denote $t$ discharged over all the hypotheses in $\Gamma$.
Then $\Delta \vdash (x :\!\!\!- s) \Rightarrow t \leadsto \bigwedge_j pq_j$
where $pq_j \cong \Gamma \Rightarrow tq_j$, with proofs
$\Delta \vdash pg_j \cong \lambda pv . 
    \overline { tg_j (pv \; sh) } ^ \Gamma : p \rightarrow pq_j$
and
$\Delta, \Theta \vdash \lambda sv .
     \overline { \overline {th}^\Xi \overrightarrow { 
         (pg_j \overrightarrow { (sg_i \; sv) } ) } }^\Gamma$
where $\Theta \cong z_0 : pq_0, ..., z_m : pq_m$.

>         consequent (Simply tqs tgs th) = do
>             pqs <- mapM (dischargeRefAlls sqs) tqs
>             pgs <- mapM wrapper tgs
>
>             freshRef ("sref" :<: PRF s) (\sref -> do
>                 th' <- dischargeLots tqs th
>                 let  sgSpine  = fmap (\sg -> A (sg $$ A (NP sref))) sgs
>                      th''     = th' $$$ fmap (\pq -> A (NP pq $$$ sgSpine)) pqs
>                 th''' <- dischargeLots sqs th''
>                 let th'''' = th''' $$$ sgSpine
>                 ph <- discharge sref th''''
>                 return (Simply pqs pgs ph)
>               )
>
>           where
>             wrapper :: (NameSupplier m) => VAL -> m VAL
>             wrapper tg = freshRef ("pref" :<: p) (\pref -> do
>                 pg <- dischargeLots sqs (tg $$ A (NP pref $$ A sh))
>                 discharge pref pg
>               )

To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder.

> propSimplify delta p@(ALL s l) = freshRef (fortran l :<: s)
>     (\refS -> forkNSupply "psAll" (forceSimplify (delta :< refS) (l $$ A (NP refS))) (thingy refS))
>   where
>     thingy :: (NameSupplier m) => REF -> Simplify -> m Simplify

If |t| is absurd, then |p| simplifies to |(x : s) => FF|. 

>     thingy refS (SimplyAbsurd prf) = freshRef ("psA" :<: PRF (ALL s (LK ABSURD)))
>         (\refA -> return (SimplyOne refA
>             (L (HF "p" (\pv -> magic (PRF (ALL s (LK ABSURD))) (prf (pv $$ A (NP refS))))))
>             (L (HF "consequentAbsurd2" (\sv -> magic (PRF (l $$ A sv)) (pval refA $$ A sv)))))
>         )

If |t| is trivial, then |p| is trivial.

>     thingy refS (SimplyTrivial prf) = do
>         prf' <- discharge refS prf
>         return (SimplyTrivial prf')

Otherwise, |p| simplifies to a conjunction of propositions |(x : s) => q| for each |q| in
the simplification of |t|.

>     thingy refS (Simply qs gs h) = do
>         pqs <- mapM (dischargeRefAlls (B0 :< refS)) qs
>         let pgs = fmap wrapper gs
>         h' <- dischargeLots qs h
>         let h'' = h' $$$ fmap (\q -> A (NP q $$ A (NP refS))) pqs
>         ph <- discharge refS h''
>         return (Simply pqs pgs ph)
>       where

The |wrapper| says how to get a proof |pg : p -> pq| given a proof |g : t -> q|.
Since |pq == (x : s) => q| we can give back a function that takes proofs
|pv : p| and |sv : s|, applies |pv| to |sv| to give a proof of |t|, then
applies |g| to this proof to get a proof of |q|.

>         wrapper :: VAL -> VAL
>         wrapper g = L (HF "p" (\pv ->
>                        L (HF "s" (\sv ->
>                            g $$ A (pv $$ A sv)))))


To simplify a blue equation, we apply the |eqGreen| operator and see what happens.
If the operator gets stuck, we give up. If we get |TRIVIAL| then we are done.
Otherwise we simplify the resulting proposition and wrap the resulting proofs
with |Con| or |Out| as appropriate.

> propSimplify delta p@(EQBLUE (sty :>: s) (tty :>: t)) = 
>     useRefl <|> unroll <|> propSearch delta p
>  where
>    useRefl :: Simplifier Simplify
>    useRefl = do
>        guard =<< (asks . equal $ SET :>: (sty, tty))
>        guard =<< (asks . equal $ sty :>: (s, t))
>        let w = pval refl $$ A sty $$ A s
>        return (SimplyTrivial w)
>
>    unroll :: Simplifier Simplify
>    unroll = case opRun eqGreen [sty, s, tty, t] of
>           Left _         -> mzero
>           Right TRIVIAL  -> return (SimplyTrivial (CON VOID))
>           Right q        -> forkNSupply "psEq" (forceSimplify delta q) equality
>          
>    equality :: Simplify -> Simplifier Simplify
>    equality (SimplyAbsurd prf) = return (SimplyAbsurd (prf . ($$ Out)))
>    equality (Simply qs gs h) = return (Simply qs
>        (fmap (..! ($$ Out)) gs)
>        (CON h))


> propSimplify delta p@(N (op :@ [sty, s, tty, t]))
>   | op == eqGreen = freshRef ("q" :<: PRF (EQBLUE (sty :>: s) (tty :>: t)))
>       (\qRef -> return (SimplyOne qRef
>           (L (HF "p" CON))
>           (NP qRef $$ Out)
>       ))


If nothing matches, we can always try searching the context.

> propSimplify delta p = propSearch delta p


The |propSearch| operation searches the context for a proof of the proposition,
and if it finds one, returns the trivial simplification. When |seekProof| finds
a proof in the context, it calls |backchain| to go under any implications and
test if the consequent matches the goal; if so, |backchain| then calls
|seekProof| to attempt to prove the hypotheses, in the context with the
backchained proposition removed. 

> propSearch :: Bwd REF -> VAL -> Simplifier Simplify
> propSearch delta p = seekProof delta F0 p >>= return . SimplyTrivial
>   where
>     seekProof :: Bwd REF -> Fwd REF -> VAL -> Simplifier VAL
>     seekProof B0 _ _ = mzero
>     seekProof (rs :< ref@(_ := DECL :<: PRF q)) fs p =
>         backchain (rs :< ref) fs B0 p q <|> seekProof rs (ref :> fs) p
>     seekProof (rs :< ref) fs p = seekProof rs (ref :> fs) p
>  
>     backchain :: Bwd REF -> Fwd REF -> Bwd REF -> VAL -> VAL -> Simplifier VAL
>     backchain rs fs ss p (ALL (PRF s) l) = freshRef ("bc" :<: PRF s)
>         (\sRef -> backchain rs fs (ss :< sRef) p (l $$ A (NP sRef)))
>                                                                       
>     backchain (rs :< ref) fs ss p q = do
>         guard =<< (asks . equal $ PROP :>: (p, q))
>         ssPrfs <- mapM (seekProof (rs <>< fs) F0 . unPRF . pty) ss
>         return (pval ref $$$ fmap A ssPrfs)
>
>     unPRF :: VAL -> VAL
>     unPRF (PRF p) = p


As a variant of |propSimplify|, |forceSimplify| guarantees to give a result,
by trying to simplify the proposition and yielding an identical copy if
simplification fails. This is useful in cases such as |&&|, where we know
we can do some simplification even if the conjuncts do not simplify.

The |forceSimplifyNamed| variant takes a name hint that will be
used if simplification fails.

> forceSimplify delta p = forceSimplifyNamed delta p ""

> forceSimplifyNamed :: Bwd REF -> VAL -> String -> Simplifier Simplify
> forceSimplifyNamed delta p hint = propSimplify delta p
>                                   <|> simplifyNone hint (PRF p)
> 
> simplifyNone :: (NameSupplier m) => String -> TY -> m Simplify
> simplifyNone hint ty = freshRef (nameHint hint ty :<: ty) (\ref ->
>     return (SimplyOne ref (idVAL "id") (NP ref)))
>   
> nameHint :: String -> VAL -> String
> nameHint hint _ | not (null hint) = hint
> nameHint _ (NP (n := _)) = "" ++ fst (last n)
> nameHint _ (L (HF s _)) = "" ++ s
> nameHint _ _ = "x"



\subsection{Problem Simplification}

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
constructing a bunch of subgoals that together solve the current goal.

> problemSimplify :: ProofState (EXTM :=>: VAL)
> problemSimplify = simplifyGoal'

> simplifyGoal' :: ProofState (EXTM :=>: VAL)
> simplifyGoal' = getHoleGoal >>= simplifyGoal . valueOf



> simplifyHypothesis :: TY -> ProofState Simplify

> simplifyHypothesis UNIT = return (SimplyTrivial VOID)

> simplifyHypothesis (SIGMA s t) = do
>     sSimp <- simplifyHypothesis s
>     case sSimp of
>         SimplyAbsurd prf -> return (SimplyAbsurd (prf . ($$ Fst)))
>         Simply srefs sbits sv -> do
>             tSimp <- simplifyHypothesis (t $$ A sv)
>             case tSimp of
>                 SimplyAbsurd prf -> return (SimplyAbsurd (prf . ($$ Snd)))
>                 Simply trefs tbits tv ->
>                     return (Simply
>                         (srefs <+> trefs)
>                         (fmap (..! ($$ Fst)) sbits
>                             <+> fmap (..! ($$ Snd)) tbits) 
>                         (PAIR sv tv))

> simplifyHypothesis (PRF p) = do
>     nsupply <- askNSupply
>     let Just s = runReaderT (forceSimplify B0 p) nsupply
>     return s

> simplifyHypothesis ty = simplifyNone "" ty



> simplifyGoal :: TY -> ProofState (EXTM :=>: VAL)

> simplifyGoal (PI s t) = do
>     sSimp <- simplifyHypothesis s
>     case sSimp of
>         SimplyAbsurd prf -> do
>             ff <- bquoteHere (L (HF "ff" (\sv ->
>                                             magic (t $$ A sv) (prf sv))))
>             give ff
>         Simply srefs bits sv -> do
>             st <- dischargePiLots srefs (t $$ A sv)
>             st' <- bquoteHere st
>             make ("" :<: st')
>             goIn
>             mapM (const (lambdaBoy "x")) srefs
>             _ :=>: tv <- simplifyGoal'
>             freshRef ("s" :<: s) (\sref -> do
>                 let v = tv $$$ fmap (A . ($$ A NP sref)) bits
>                 v' <- bquote (B0 :< sref) v
>                 give (L (fortran t :. v'))
>               )

> simplifyGoal UNIT = give VOID
> simplifyGoal (SIGMA s t) = do
>     stm <- bquoteHere s
>     make (fortran t :<: stm)
>     goIn
>     stm' :=>: sv <- simplifyGoal s
>     let t' = t $$ A sv
>     ttm <- bquoteHere t'
>     make ("" :<: ttm)
>     goIn
>     ttm' :=>: tv <- simplifyGoal t'
>     give (PAIR (N stm') (N ttm'))

> simplifyGoal (PRF p) = do
>     optional propSimplifyHere
>     getMotherDefinition <* goOut

> simplifyGoal _ = getMotherDefinition <* goOut



\subsection{Invoking Simplification}

The |propSimplifyHere| command attempts propositional simplification on the
current location, which must be an open goal of type |PRF p| for some |p|.
If it is unable to simplify |p| or simplifies it to |FF|, it will fail and
throw an error. Otherwise, it will create zero or more new subgoals
(from the conjuncts of the simplified proposition, if any), solve the
current goal with the subgoals, and return a list of them.

> propSimplifyHere :: ProofState (Bwd (EXTM :=>: VAL))
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     nsupply <- askNSupply
>     case runReaderT (propSimplify B0 p) nsupply of
>         Nothing                   -> throwError' $ err "propSimplifyHere: unable to simplify."
>         Just (SimplyAbsurd _)     -> throwError' $ err "propSimplifyHere: oh no, goal is absurd!"
>
>         Just (SimplyTrivial prf)  -> bquoteHere prf >>= give' >> return B0
>
>         Just (Simply qs _ h) -> do
>             qrs  <- mapM makeSubgoal qs
>             h'   <- dischargeLots qs h
>             prf  <- bquoteHere (h' $$$ fmap (A . valueOf) qrs)
>             give' prf
>             return qrs

The |makeSubgoal| command makes a new subgoal whose type corresponds to the type
of the given reference, and returns its term and value representations.

> makeSubgoal :: REF -> ProofState (EXTM :=>: VAL)
> makeSubgoal ref = do
>     q'  <- bquoteHere (pty ref)
>     x   <- pickName "q" (fst (last (refName ref)))
>     make (x :<: q')


The |simplify| tactic attempts to simplify the type of the current goal, which
should be propositional.

> simplifyCTactic :: ProofState String
> simplifyCTactic = do
>     subs <- propSimplifyHere 
>     case subs of
>         B0  -> return "Solved."
>         _   -> do
>             subStrs <- mapM (prettyType . termOf)  subs
>             nextGoal
>             return ("Simplified to:\n" ++ 
>                         foldMap (\s -> s ++ "\n") subStrs)
>   where
>     prettyType :: EXTM -> ProofState String
>     prettyType tm = do
>         (_ :<: ty) <- inferHere tm
>         ty' <- bquoteHere ty
>         d <- prettyHere (SET :>: ty')
>         return (renderHouseStyle d)

> import -> CochonTactics where
>   : nullaryCT "propsimplify" simplifyCTactic
>       "propsimplify - applies propositional simplification to the current goal."
>   : nullaryCT "simplify" (problemSimplify >> return "Simplified.")
>       "simplify - simplifies the current problem."