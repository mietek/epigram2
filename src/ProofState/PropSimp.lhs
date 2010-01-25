%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances #-}

> module ProofState.PropSimp where

> import Debug.Trace

> import Control.Applicative 
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
>     return (SimplyOne ref idVAL (NP ref)))
>   where
>     nameHint :: VAL -> String
>     nameHint (NP (n := _)) = "__" ++ fst (last n)
>     nameHint (L (HF s _)) = "__" ++ s
>     nameHint _ = "__simplifyNone"

The |propSimplifyHere| command attempts propositional simplification on the
current location, which must be an open goal of type |PRF p| for some |p|.
If it successfully simplifies the goal proposition, it will create a new goal
and solve the current one with an appropriate coercion. If it simplifies the
goal to |TT|, it will simply solve the current goal. If it simplifies the goal
to |FF|, it will complain.

> propSimplifyHere :: ProofState ()
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     nsupply <- askNSupply
>     let simp = propSimplify B0 p nsupply
>     case simp of
>         SimplyTrivial prf -> do
>             prf' <- bquoteHere prf
>             give prf'
>             return ()

>         SimplyAbsurd _ -> throwError' "propSimplifyHere: oh no, goal is absurd!"

>         si@(Simply qs _ h) -> do
>             qrs <- mapM (\ref -> do
>                 q' <- bquoteHere (pty ref)
>                 x <- pickName "q" ""
>                 qr <- make (x :<: q')
>                 return (A (evTm qr))
>               ) qs

>             h' <- dischargeLots qs h
>             prf <- bquoteHere (h' $$$ qrs)
>             giveNext prf
>             return ()
                 

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

> idVAL :: VAL
> idVAL = L (HF "__id" id)

> instance Show (VAL -> VAL) where
>   show v = "(...)"


The |propSimplify| command takes a proposition and attempts to simplify it. At the
moment it only requires a name supply, but it really should take a context as well.

> propSimplify :: (NameSupplier m) => Bwd REF -> VAL -> m Simplify


Simplifying |TT| and |FF| is remarkably easy.

> propSimplify _ ABSURD   = return (SimplyAbsurd   id)
> propSimplify _ TRIVIAL  = return (SimplyTrivial  VOID)


To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify delta (AND p1 p2) = forkNSupply "__psAnd1" (propSimplify delta p1)
>     (\ p1Simp -> forkNSupply "__psAnd2" (propSimplify delta p2)
>         (\ p2Simp ->
>             return (simplifyAnd p1Simp p2Simp)))


To simplify |p = (x :- s) => t|, we first try to simplify |s|:

> propSimplify delta p@(ALL (PRF s) l@(L sc)) = forkNSupply "__psImp1" (propSimplify delta s)
>     (\simpS -> case {-|trace ("\npropSimplify: simpS = " ++ show simpS)|-} simpS of

If |s| is absurd then |p| is trivial, which we can prove by doing |magic| whenever someone
gives us an element of |s|.

>         SimplyAbsurd prfAbsurdS -> return (SimplyTrivial
>             (L (HF "__antecedentAbsurd" (\sv -> magic (PRF (l $$ A sv)) (prfAbsurdS sv)))))

If |s| is trivial, then we go under the binder by applying the proof, and then simplify |t|.
Then |p| simplifies to the result of simplifying |t|, with the proofs constructed by 
$\lambda$-abstracting in one direction and applying the proof of |s| in the other direction.

>         SimplyTrivial prfS -> forkNSupply "__psImp2" (propSimplify delta (l $$ A prfS))
>             (\simpT -> case {-|trace ("\ntrivial, simpT = " ++ show simpT)|-} simpT of
>                 SimplyAbsurd prfAbsurdT -> return (SimplyAbsurd (prfAbsurdT . ($$ A prfS)))
>                 SimplyTrivial prfT -> return (SimplyTrivial (LK prfT))
>                 Simply tqs tgs th -> return (Simply tqs
>                     (fmap (\g -> L (HF "__x" (\v -> g $$ A (v $$ A prfS)))) tgs)
>                     (LK th))
>             )

If |s| simplifies nontrivially, we have a bit more work to do. We simplify |t| under the binder
by adding the simplified conjuncts of |s| to the context and applying |l| to |sh| (the proof of
|s| in the extended context). 

>         Simply sqs sgs sh -> forkNSupply "__psImp3" (propSimplify (delta <+> sqs) (l $$ A sh))
>             (\simpT -> case {-|trace ("\nsimplified, simpT = " ++ show simpT)|-} simpT of
>                 SimplyAbsurd prfAbsurdT -> do
>                     madness <- dischargeAllLots sqs (PRF ABSURD)
>                     freshRef ("__madness" :<: madness) (\ref -> 
>                         freshRef ("__pref" :<: p) (\pref -> do
>                             g <- dischargeLots sqs (prfAbsurdT (NP pref $$ A sh))
>                             g' <- discharge pref g
>                             return (SimplyOne ref
>                                 (L (HF "__p" (\pv -> g' $$ A pv)))
>                                 (L (HF "__consequentAbsurd" (\sv -> magic (PRF (l $$ A sv))
>                                 (NP ref $$$ (fmap (A . ($$ A sv)) sgs))))))
>                           )
>                       )

If the consequent |t| is trivial, then the implication is trivial, which we can prove as
follows:
\begin{enumerate}
\item Discharge the proof of |t| over the conjuncts |sqs| to get a $\lambda$-lifted proof |prfT'|.
\item Construct a proof of |(x :\!\!- s) => t| that takes a proof of |s| and applies the proofs
|sgs| to get proofs of the |sqs|, which can then be passed to |prfT'| to get a proof of |t|.
\end{enumerate}

>                 SimplyTrivial prfT -> do
>                     prfT' <- dischargeLots sqs prfT
>                     return (SimplyTrivial (L (HF "__consequentTrivial" (\sv ->
>                         prfT' $$$ (fmap (A . ($$ A sv)) sgs)))))

Otherwise, if the consequent |t| simplifies to a conjunction |tqs| with proofs |tg : t -> tq|,
and proof |th| of |t| in the context |delta <+> sqs|, we proceed as follows:
\begin{enumerate}
\item Discharge the antecedents |sqs| over each conjunct in the consequent to produce a
      conjunction |pqs|.
\item Construct the proofs |pg : p -> pq| from the |tgs| thus:
      \begin{enumerate}
        \item Declare |pref| to be a reference of type |(x : s) => t|.
        \item Apply |pref| to the proof of |s| in the context |delta <+> sqs|, giving a value
              of type |t|, to which |tg| can be applied to produce a proof of |tq|.
        \item Discharge the proof of |tq| over the |sqs| to produce a proof of |pq|.
        \item Discharge |pref| and return the function that, given a proof of |p|, applies
              the discharged term to it.
      \end{enumerate}
\item Construct the proof |ph| of |p| in the context |pqs| thus:
      \begin{enumerate}
        \item Discharge the proof |th| of |t| over the conjuncts |tqs| to produce |th'|.
        \item Apply |th'| to the proofs of the |tqs| (created by applying the |pqs| to the |sqs|)
              to produce |th''|.
        \item Discharge |th''| over the |sqs| to give a function |th'''| from proofs of the |sqs|
              to proofs of |t|.
        \item Construct the proof of |p| that, given a proof of |s|, applies the |sgs| to it to
              produce proofs of the |sqs|, and applies them to |th'''| to get a proof of |t|.
      \end{enumerate}
\end{enumerate}

>                 Simply tqs tgs th -> do
>                     pqs <- mapM (dischargeRefAlls sqs) tqs
>
>                     pgs <- mapM (\tg -> freshRef ("__pref" :<: p) (\pref -> do
>                         pg <- dischargeLots sqs (tg $$ A (NP pref $$ A sh))
>                         discharge pref pg
>                       )) tgs
>
>                     freshRef ("__sref" :<: PRF s) (\sref -> do
>                         let sgSpine = fmap (\sg -> A (sg $$ A (NP sref))) sgs
>                         th' <- dischargeLots tqs th
>                         let th'' = th' $$$ fmap (\pq -> A (NP pq $$$ sgSpine)) pqs
>                         th''' <- dischargeLots sqs th''
>                         let th'''' = th''' $$$ sgSpine
>                         ph <- discharge sref th''''
>                         return (Simply pqs pgs ph)
>                       )

>               ) -- simpT
>       ) -- simpS

To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder. If |t| is absurd, then |p|
simplifies to |(x : s) => FF|. If |t| is trivial, then |p| is trivial. Otherwise,
|p| simplifies to a conjunction of propositions |(x : s) => q| for each |q| in
the simplification of |t|.

> propSimplify delta p@(ALL s l@(L sc)) = freshRef (fortran l :<: s) (\refS -> 
>   forkNSupply "__psAll" (propSimplify (delta :< refS) (l $$ A (NP refS)))
>     (\simpL -> case simpL of
>         SimplyAbsurd prf -> freshRef ("__psA" :<: PRF (ALL s (LK ABSURD))) (\refA ->
>             return (SimplyOne refA
>                 (L (HF "__p" (\pv -> magic (PRF (ALL s (LK ABSURD))) (prf (pv $$ A (NP refS))))))
>                 (L (HF "__consequentAbsurd2" (\sv -> magic (PRF (l $$ A sv)) (pval refA $$ A sv))))))

>         SimplyTrivial prf -> do
>             prf' <- discharge refS prf
>             return (SimplyTrivial prf')

>         Simply qs gs h -> do
>             qs' <- mapM (dischargeRefAlls (B0 :< refS)) qs
>             let gs' = fmap (\g -> (L (HF "__p" (\pv -> (L (HF "__consequentSimplified2" (\sv -> g $$ A (pv $$ A sv)))))))) gs
>             h' <- dischargeLots qs h
>             let h'' = h' $$$ fmap (\q -> (A (NP q $$ A (NP refS)))) qs'
>             h''' <- discharge refS h''
>             return (Simply qs' gs' h''')
>             
>   
>   ))


To simplify a neutral parameter, we look for a proof in the context. 

> propSimplify delta (NP p) = do
>     nsupply <- askNSupply
>     case seekType delta (PRF (NP p)) nsupply of
>         Just ref -> return (SimplyTrivial (pval ref))
>         Nothing -> simplifyNone (NP p)
>   where
>     seekType :: Bwd REF -> TY -> NameSupply -> Maybe REF
>     seekType B0 _ = return Nothing
>     seekType (rs :< ref) ty = do
>         b <- equal (SET :>: (pty ref, ty))
>         if b then return (Just ref) else seekType rs ty


If nothing matches, we are unable to simplify this term.

> propSimplify _ tm = simplifyNone tm


The |simplifyAnd| function takes the results of simplifying two conjuncts and
returns a simplified conjunction.

> simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

> simplifyAnd (SimplyAbsurd prf) _ = SimplyAbsurd (prf . ($$ Fst))
> simplifyAnd _ (SimplyAbsurd prf) = SimplyAbsurd (prf . ($$ Snd))
         
Otherwise, we can simplify the conjunction:

> simplifyAnd (Simply q1s g1s h1) (Simply q2s g2s h2) =
>     Simply (q1s <+> q2s)
>         (fmap (\g -> L (HF "__x" (\v -> g $$ A (v $$ Fst)))) g1s <+> (fmap (\g -> L (HF "__x" (\v -> g $$ A (v $$ Snd)))) g2s))
>         (PAIR h1 h2)



> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >> return "Simplified.")
>       "simplify - applies propositional simplification to the current goal."