%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances #-}

> module ProofState.PropSimp where

> import Debug.Trace

> import Control.Applicative 
> import Control.Monad.Reader hiding (mapM)
> import Data.Foldable
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import DisplayLang.DisplayTm
> import DisplayLang.Elaborator
> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.ProofState
> import ProofState.ProofKit

> import Prelude hiding (foldl, mapM)

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

> simplifyNone :: (NameSupplier m) => VAL -> m Simplify
> simplifyNone p = freshRef (nameHint p :<: PRF p) (\ref ->
>     return (SimplyOne ref (L (HF "__id" id)) (NP ref)))
>   where
>     nameHint :: VAL -> String
>     nameHint (NP (n := _)) = "__" ++ fst (last n)
>     nameHint (L (HF s _)) = "__" ++ s
>     nameHint _ = "__simplifyNone"


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

> dischargeAllLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeAllLots bs v = do
>     v' <- bquote bs v
>     v'' <- wrapAlls bs v'
>     return (evTm v'')
>   where
>     wrapAlls :: (NameSupplier m) => Bwd REF -> INTM -> m INTM
>     wrapAlls B0 tm = return tm
>     wrapAlls (bs :< (n := _ :<: ty)) (PRF tm) = do
>         ty' <- bquote B0 ty
>         wrapAlls bs (PRF (ALL ty' (L (fst (last n) :. tm))))


The |dischargeRefAlls| function calls |dischargeAllLots| on the type of a reference.

> dischargeRefAlls :: (NameSupplier m) => Bwd REF -> REF -> m REF
> dischargeRefAlls bs (n := DECL :<: ty) = do
>     ty' <- dischargeAllLots bs ty
>     return (n := DECL :<: ty')


The |magic ty| function takes a proof of |FF| and yields a value of type |ty|.

> magic :: TY -> VAL -> VAL
> magic ty no = nEOp @@ [no, ty]


The |...| operator is composition of |VAL| functions.

> (...) :: VAL -> VAL -> VAL
> f ... g = L (HF "__x" (\x -> f $$ A (g $$ A x)))

The curiously more useful |..!| operator is composition of a genuine |VAL|
function with a |VAL -> VAL| function.

> (..!) :: VAL -> (VAL -> VAL) -> VAL
> f ..! g = L (HF "__x" (\x -> f $$ A (g x)))


\subsection{Simplification in Action}

The |propSimplify| command takes a proposition and attempts to simplify it.

> propSimplify :: Bwd REF -> VAL -> Simplifier Simplify


Simplifying |TT| and |FF| is remarkably easy.

> propSimplify _ ABSURD   = return (SimplyAbsurd   id)
> propSimplify _ TRIVIAL  = return (SimplyTrivial  VOID)


To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify delta (AND p1 p2) = forkNSupply "__psAnd1" (forceSimplify delta p1)
>     (\ p1Simp -> forkNSupply "__psAnd2" (forceSimplify delta p2)
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

> propSimplify delta p@(ALL (PRF s) l@(L sc)) =
>     forkNSupply "__psImp1" (forceSimplify delta s) antecedent
>   where
>     antecedent :: Simplify -> Simplifier Simplify

If |s| is absurd then |p| is trivial, which we can prove by doing |magic|
whenever someone gives us an element of |s|.

>     antecedent (SimplyAbsurd prfAbsurdS) = return (SimplyTrivial
>         (L (HF "__antecedentAbsurd" (\sv ->
>             magic (PRF (l $$ A sv)) (prfAbsurdS sv)))))

If |s| is trivial, then we go under the binder by applying the proof, and then
simplify |t|. Then |p| simplifies to the result of simplifying |t|, with the
proofs constructed by $\lambda$-abstracting in one direction and applying the
proof of |s| in the other direction.

>     antecedent (SimplyTrivial prfS) =
>         forkNSupply "__psImp2" (forceSimplify delta (l $$ A prfS)) consequentTrivial
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
>         forkNSupply "__psImp3" (forceSimplify (delta <+> sqs) (l $$ A sh)) consequent
>       where
>         consequent :: Simplify -> Simplifier Simplify
>         consequent (SimplyAbsurd prfAbsurdT) = do
>             madness <- dischargeAllLots sqs (PRF ABSURD)
>             freshRef ("__madness" :<: madness) (\ref -> 
>                 freshRef ("__pref" :<: p) (\pref -> do
>                     g <- dischargeLots sqs (prfAbsurdT (NP pref $$ A sh))
>                     g' <- discharge pref g
>                     return (SimplyOne ref
>                         (L (HF "__p" (\pv -> g' $$ A pv)))
>                         (L (HF "__consequentAbsurd" (\sv -> magic (PRF (l $$ A sv))
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
>             return (SimplyTrivial (L (HF "__consequentTrivial" (\sv ->
>                 prfT' $$$ (fmap (A . ($$ A sv)) sgs)))))

Otherwise, if the consequent |t| simplifies to a conjunction |tqs| with proofs |tg : t -> tq|,
and proof |th| of |t| in the context |delta <+> sqs|, we proceed as follows.
\question{Is there a better way of explaining this than a bunch of scribbles on a whiteboard?}
\begin{enumerate}
\item Discharge the antecedents |sqs| over each conjunct in the consequent to produce a
      conjunction |pqs|.
\item Construct the proofs |pg : p -> pq| from the |tgs| thus:
      \begin{enumerate}
        \item Declare |pref| to be a reference of type |(x : s) => t|.
        \item Apply |pref| to the proof of |s| in the context |delta <+> sqs|, giving a value
              of type |t|, to which |tg| can be applied to produce a proof of |tq|.
        \item Discharge the proof of |tq| over the |sqs| to produce a proof of |pq|.
        \item Discharge |pref| to produce the required proof.
      \end{enumerate}
\item Construct the proof |ph| of |p| in the context |pqs| thus:
      \begin{enumerate}
        \item Declare |sref| to be a reference of type |s|.
        \item Discharge the proof |th| of |t| over the conjuncts |tqs| to produce |th'|.
        \item Let |sgSpine| be the spine of |sgs| applied to |sref| to produce proofs of the |sqs|.
        \item Apply |th'| to each proof of a |tq| (created by applying a |pq| to the |sgSpine|),
              to produce |th''|.
        \item Discharge |th''| over the |sqs| to give a function |th'''| from proofs of the |sqs|
              to proofs of |t|.
        \item Apply |th'''| to the |sgSpine| and discharge |sref| to produce a function |ph| that,
              given a proof of |s|, yields a proof of |t|.
      \end{enumerate}
\end{enumerate}

>         consequent (Simply tqs tgs th) = do
>             pqs <- mapM (dischargeRefAlls sqs) tqs
>             pgs <- mapM wrapper tgs
>
>             freshRef ("__sref" :<: PRF s) (\sref -> do
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
>             wrapper tg = freshRef ("__pref" :<: p) (\pref -> do
>                 pg <- dischargeLots sqs (tg $$ A (NP pref $$ A sh))
>                 discharge pref pg
>               )

To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder.

> propSimplify delta p@(ALL s l@(L sc)) = freshRef (fortran l :<: s)
>     (\refS -> forkNSupply "__psAll" (forceSimplify (delta :< refS) (l $$ A (NP refS))) (thingy refS))
>   where
>     thingy :: (NameSupplier m) => REF -> Simplify -> m Simplify

If |t| is absurd, then |p| simplifies to |(x : s) => FF|. 

>     thingy refS (SimplyAbsurd prf) = freshRef ("__psA" :<: PRF (ALL s (LK ABSURD)))
>         (\refA -> return (SimplyOne refA
>             (L (HF "__p" (\pv -> magic (PRF (ALL s (LK ABSURD))) (prf (pv $$ A (NP refS))))))
>             (L (HF "__consequentAbsurd2" (\sv -> magic (PRF (l $$ A sv)) (pval refA $$ A sv)))))
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
>         wrapper g = L (HF "__p" (\pv ->
>                        L (HF "__s" (\sv ->
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

>    unroll :: Simplifier Simplify
>    unroll = case opRun eqGreen [sty, s, tty, t] of
>           Left _         -> mzero
>           Right TRIVIAL  -> return (SimplyTrivial (CON VOID))
>           Right q        -> forkNSupply "__psEq" (forceSimplify delta q) equality
>          
>    equality :: Simplify -> Simplifier Simplify
>    equality (SimplyAbsurd prf) = return (SimplyAbsurd (prf . ($$ Out)))
>    equality (Simply qs gs h) = return (Simply qs
>        (fmap (..! ($$ Out)) gs)
>        (CON h))


> propSimplify delta p@(N (op :@ [sty, s, tty, t]))
>   | op == eqGreen = freshRef ("__q" :<: PRF (EQBLUE (sty :>: s) (tty :>: t)))
>       (\qRef -> return (SimplyOne qRef
>           (L (HF "__p" CON))
>           (NP qRef $$ Out)
>       ))


If nothing matches, we can always try searching the context.

> propSimplify delta p = propSearch delta p


As a variant of |propSimplify|, |forceSimplify| guarantees to give a result
by trying to simplify the proposition and yielding an identical copy if
simplification fails.

> forceSimplify :: Bwd REF -> VAL -> Simplifier Simplify
> forceSimplify delta p = propSimplify delta p <|> simplifyNone p


The |propSearch| operation looks in the context for a proof of the proposition,
and if it finds one, returns the trivial simplification.

> propSearch :: Bwd REF -> VAL -> Simplifier Simplify
> propSearch delta p = do
>     ref <- seekType delta (PRF p)
>     return (SimplyTrivial (pval ref))
>   where
>     seekType :: Bwd REF -> TY -> Simplifier REF
>     seekType B0 _ = mzero
>     seekType (rs :< ref) ty = (do
>         guard =<< (asks . equal $ SET :>: (pty ref, ty))
>         return ref
>       ) <|> seekType rs ty




\subsection{Invoking Simplification}

The |propSimplifyHere| command attempts propositional simplification on the
current location, which must be an open goal of type |PRF p| for some |p|.
If it simplifies the goal to |TT|, it will simply solve the goal and return |True|.
If it simplifies the goal to |FF|, it will fail and throw an error.
Otherwise, it will create one or more new subgoals (from the conjuncts of the
simplified proposition) and solve the current goal with them.

> propSimplifyHere :: ProofState Bool
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     nsupply <- askNSupply
>     case runReaderT (propSimplify B0 p) nsupply of
>         Nothing -> throwError' "propSimplifyHere: unable to simplify"
>         Just (SimplyAbsurd _) -> throwError' "propSimplifyHere: oh no, goal is absurd!"
>
>         Just (SimplyTrivial prf) -> bquoteHere prf >>= give >> return True
>
>         Just (Simply qs _ h) -> do
>             qrs  <- mapM makeSubgoal qs
>             h'   <- dischargeLots qs h
>             prf  <- bquoteHere (h' $$$ qrs)
>             giveNext prf
>             return False
>  where

The |makeSubgoal| command makes a new subgoal whose type corresponds to the type
of the given reference, and returns the eliminator that applies a reference to
the new subgoal.

>    makeSubgoal :: REF -> ProofState (Elim VAL)
>    makeSubgoal ref = do
>        q'  <- bquoteHere (pty ref)
>        x   <- pickName "q" ""
>        qr  <- make (x :<: q')
>        return (A (evTm qr))


The |simplify| tactic attempts to simplify the type of the current goal, which
should be propositional.

> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >>= \b -> return (if b then "Solved." else "Simplified."))
>       "simplify - applies propositional simplification to the current goal."