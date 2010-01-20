%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState.PropSimp where

> import Control.Applicative

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply

> import DisplayLang.DisplayTm
> import DisplayLang.Elaborator
> import DisplayLang.Naming

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.ProofState
> import ProofState.ProofKit

%endif

\section{Propositional Simplification}

The result of simplifying a proposition $p$ may be:
\begin{description}
\item{|SimplifyNone|}, no progress;
\item{|SimplifyAbsurd prf|}, a proof |prf| of |p => FF|;
\item{|SimplifyTrivial prf|}, a proof |prf| of |p|; or
\item{|SimplifyTo q prfQP prfPQ |}, a conjunction of propositions |q| with
a proof |prfQP| that $q \Rightarrow p$ and a proof |prfPQ| that |p => q|.
\end{description}

> data Simplify  =  SimplifyNone
>                |  SimplifyAbsurd VAL
>                |  SimplifyTrivial VAL
>                |  SimplifyTo VAL VAL VAL


> propSimplifyHere :: ProofState ()
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     case propSimplify p of
>         SimplifyTrivial prf  -> do
>             equiv <- bquoteHere (coe @@ [PRF TRIVIAL, PRF p,
>                                          CON (PAIR (L (K prf)) (L (K VOID))), VOID])
>             prf' <- bquoteHere prf
>             proofTrace . unlines $ ["Simplified to TRIVIAL with proof", show prf']
>             give equiv
>             return ()
>         SimplifyTo q prfQP prfPQ  -> do
>             q' <- bquoteHere (PRF q)
>             x <- pickName "q" ""
>             qr <- make (x :<: q')
>             equiv <- bquoteHere (coe @@ [PRF q, PRF p, CON (PAIR prfQP prfPQ),
>                                    evTm qr])
>             prfQP' <- bquoteHere prfQP
>             prfPQ' <- bquoteHere prfPQ
>             proofTrace . unlines $ ["Simplified to", show q', "with Q => P by",
>                                     show prfQP', "and P => Q by", show prfPQ',
>                                     "yielding equivalence", show equiv]
>             give equiv
>             return ()
>         SimplifyNone      -> throwError' "propSimplifyHere: cannot simplify."
>         SimplifyAbsurd _  -> throwError' "propSimplifyHere: oh no, goal is absurd!"
                    

> conjunct :: [VAL] -> VAL
> conjunct [] = TRIVIAL
> conjunct qs = foldr1 AND qs

> idVAL :: VAL
> idVAL = L (HF "__id" id)


> forceSimplify :: VAL -> Simplify
> forceSimplify p = case propSimplify p of
>     SimplifyNone -> SimplifyTo p idVAL idVAL
>     SimplifyAbsurd prf -> SimplifyTo ABSURD
>         (L (HF "__absurd" (\no -> nEOp @@ [no, PRF p]))) prf
>     SimplifyTrivial prf -> SimplifyTo TRIVIAL (L (K prf)) (L (K VOID))
>     st -> st

> makeSimplify :: VAL -> VAL -> VAL -> Simplify
> makeSimplify TRIVIAL prf _ = SimplifyTrivial (prf $$ A VOID)
> makeSimplify ABSURD _ prf  = SimplifyAbsurd prf
> makeSimplify q prfQP prfPQ = SimplifyTo q prfQP prfPQ


> propSimplify :: VAL -> Simplify


> propSimplify ABSURD     = SimplifyAbsurd idVAL


> propSimplify TRIVIAL    = SimplifyTrivial VOID


> propSimplify (AND p q)  = case (propSimplify p, propSimplify q) of

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

>     (SimplifyAbsurd prf, _) ->
>         SimplifyAbsurd (L (HF "__absurd" (\pq -> prf $$ A (pq $$ Fst))))

>     (_, SimplifyAbsurd prf) ->
>         SimplifyAbsurd (L (HF "__absurd" (\pq -> prf $$ A (pq $$ Snd))))

If both propositions are trivial, then their conjunction is trivial:

>     (SimplifyTrivial prfP, SimplifyTrivial prfQ) ->
>         SimplifyTrivial (PAIR prfP prfQ)

If one of them is trivial, then we can simplify to the other:

>     (SimplifyTrivial prfP, SimplifyNone) ->
>         SimplifyTo q (L (HF "__q" (\qv -> PAIR prfP qv)))
>                      (L (HF "__pq" (\pqv -> pqv $$ Snd)))

>     (SimplifyTrivial prfP, SimplifyTo s prfSQ prfQS) ->
>         SimplifyTo s (L (HF "__s" (\sv -> PAIR prfP (prfSQ $$ A sv))))
>                      (L (HF "__pq" (\pqv -> prfQS $$ A (pqv $$ Snd))))

>     (SimplifyNone, SimplifyTrivial prfQ) ->
>         SimplifyTo p (L (HF "__p" (\pv -> PAIR pv prfQ)))
>                      (L (HF "__pq" (\pqv -> pqv $$ Fst)))

>     (SimplifyTo r prfRP prfPR, SimplifyTrivial prfQ) ->
>         SimplifyTo r (L (HF "__r" (\rv -> PAIR (prfRP $$ A rv) prfQ)))
>                      (L (HF "__pq" (\pqv -> prfPR $$ A (pqv $$ Fst))))

If one or both of them simplifies, we can simplify the conjunction:

>     (SimplifyTo r prfRP prfPR, SimplifyNone) ->
>         SimplifyTo (AND r q)
>             (L (HF "__rq" (\rqv ->
>                 PAIR (prfRP $$ A (rqv $$ Fst)) (rqv $$ Snd))))
>             (L (HF "__pq" (\pqv ->
>                 PAIR (prfPR $$ A (pqv $$ Fst)) (pqv $$ Snd))))

>     (SimplifyNone, SimplifyTo s prfSP prfPS) ->
>         SimplifyTo (AND p s)
>             (L (HF "__ps" (\psv ->
>                 PAIR (psv $$ Fst) (prfSP $$ A (psv $$ Snd)))))
>             (L (HF "__pq" (\pqv ->
>                 PAIR (pqv $$ Fst) (prfPS $$ A (pqv $$ Snd)))))

>     (SimplifyTo r prfRP prfPR, SimplifyTo s prfSQ prfQS) ->
>         SimplifyTo (AND r s)
>             (L (HF "__rs" (\rs ->
>                 PAIR (prfRP $$ A (rs $$ Fst)) (prfSQ $$ A (rs $$ Snd)))))
>             (L (HF "__pq" (\pq ->
>                 PAIR (prfPR $$ A (pq $$ Fst)) (prfQS $$ A (pq $$ Snd)))))

>     _ -> SimplifyNone


> propSimplify (ALL (PRF r) s) = case propSimplify r of
>     SimplifyAbsurd prf -> SimplifyTrivial
>         (L (HF "__r" (\rv -> nEOp @@ [prf $$ A rv, PRF (s $$ A rv)])))

>     SimplifyTrivial prfR ->
>         let  SimplifyTo t prfTS prfST = forceSimplify (s $$ A VOID)
>         in   makeSimplify t
>                 (L (HF "__t" (\tv -> L (K (prfTS $$ A tv)))))
>                 (L (HF "__rtos" (\rtosv -> prfST $$ A (rtosv $$ A prfR))))

>     _ -> SimplifyNone


> propSimplify tm         = SimplifyNone






> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >> return "Simplified.")
>       "simplify - applies propositional simplification to the current goal."