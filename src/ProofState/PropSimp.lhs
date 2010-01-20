%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState.PropSimp where

> import Control.Applicative

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

%endif

\section{Propositional Simplification}

A \emph{normal} proposition is either |FF| or a conjunction of \emph{q-neutral}
propositions. \question{What should the terminology be?}
A \emph{q-neutral} proposition is either:
\begin{itemize}
\item a neutral term of type |Prop|;
\item a blue equation with (at least) one neutral side;
\item |(x : S) => P|, with |S| not a proof and |P| q-neutral; or
\item |(x :- P) => Q|, with |P| and |Q| q-neutral and |P| not |FF|.
\end{itemize}
A q-neutral context is a context all of whose propositions are q-neutral.

Given a proposition |p|, the propositional simplifier should produce an
equivalent proposition |p'| together with proofs of |p' => p| and |p => p'|.

The result of simplifying a proposition $p$ may be:
\begin{description}
\item{|SimplifyNone p|}, no progress;
\item{|SimplifyAbsurd prf|}, a proof |prf| of |p => FF|;
\item{|SimplifyTrivial prf|}, a proof |prf| of |p|; or
\item{|SimplifyTo q prfQP prfPQ |}, a conjunction of propositions |q| with
a proof |prfQP| that $q \Rightarrow p$ and a proof |prfPQ| that |p => q|.
\end{description}

> data Simplify  =  SimplifyNone VAL
>                |  SimplifyAbsurd VAL
>                |  SimplifyTrivial VAL
>                |  SimplifyTo VAL VAL VAL


The |propSimplifyHere| command attempts propositional simplification on the
current location, which must be an open goal of type |PRF p| for some |p|.
If it successfully simplifies the goal proposition, it will create a new goal
and solve the current one with an appropriate coercion. If it simplifies the
goal to |TT|, it will simply solve the current goal. If it simplifies the goal
to |FF|, it will complain.

> propSimplifyHere :: ProofState ()
> propSimplifyHere = do
>     (_ :=>: PRF p) <- getHoleGoal
>     simp <- propSimplify p
>     case simp of
>         SimplifyTrivial prf  -> do
>             let equiv = coe @@ [PRF TRIVIAL, PRF p,
>                                          CON (PAIR (L (K prf)) (L (K VOID))), VOID]
>             proofTrace . unlines $ ["Simplified to TRIVIAL with proof", show prf]
>             equiv' <- bquoteHere equiv
>             prf' <- bquoteHere prf
>             proofTrace . unlines $ ["which bquotes to", show prf']
>             give equiv'
>             return ()
>         SimplifyTo q prfQP prfPQ  -> do
>             q' <- bquoteHere (PRF q)
>             x <- pickName "q" ""
>             qr <- make (x :<: q')
>             let equiv = coe @@ [PRF q, PRF p, CON (PAIR prfQP prfPQ), evTm qr]
>             proofTrace . unlines $ ["Simplified to", show q, "with Q => P by",
>                                     show prfQP, "and P => Q by", show prfPQ,
>                                     "yielding equivalence", show equiv]
>             equiv' <- bquoteHere equiv
>             prfQP' <- bquoteHere prfQP
>             prfPQ' <- bquoteHere prfPQ
>             proofTrace . unlines $ ["(BQ) Simplified to", show q', "with Q => P by",
>                                     show prfQP', "and P => Q by", show prfPQ',
>                                     "yielding equivalence", show equiv']
>             giveNext equiv'
>             return ()
>         SimplifyNone    _ -> throwError' "propSimplifyHere: cannot simplify."
>         SimplifyAbsurd  _ -> throwError' "propSimplifyHere: oh no, goal is absurd!"
                    

Here are a couple of shortcuts for writing proof values. The |idVAL| value
represents the identity function, and |magic ty| represents the function that
takes a proof of |FF| and yields a value of type |ty|.

> idVAL :: VAL
> idVAL = L (HF "__id" id)
>
> magic :: TY -> VAL
> magic ty = L (HF "__absurd" (\no -> nEOp @@ [no, ty]))


The |forceSimplify| function takes a proposition and the result of simplifying it,
and yields a |SimplifyTo| version.

> forceSimplify :: VAL -> Simplify -> Simplify
> forceSimplify _ (SimplifyNone p)       = SimplifyTo p idVAL idVAL
> forceSimplify p (SimplifyAbsurd prf)   = SimplifyTo ABSURD (magic (PRF p)) prf
> forceSimplify _ (SimplifyTrivial prf)  = SimplifyTo TRIVIAL (LK prf) (LK VOID)
> forceSimplify _ (SimplifyTo p a b)     = SimplifyTo p a b

The |makeSimplify| function is a smart constructor for |Simplify| that produces
|SimplifyTrivial|, |SimplifyAbsurd| or |SimplifyTo| as appropriate.

> makeSimplify :: VAL -> VAL -> VAL -> Simplify
> makeSimplify TRIVIAL prf _ = SimplifyTrivial (prf $$ A VOID)
> makeSimplify ABSURD _ prf  = SimplifyAbsurd prf
> makeSimplify q prfQP prfPQ = SimplifyTo q prfQP prfPQ


The |curryProp| function takes a conjunction and a consequent, and produces a
curried proposition that has the pieces of the conjunction as individual
antecedents, followed by the given consequent. Thus
|curryProp (A && B && C) D == (A => B => C => D)|.

> curryProp :: VAL -> VAL -> VAL
> curryProp ps q = curryList $ flattenAnd (AND ps q)
>   where
>     flattenAnd :: VAL -> [VAL]
>     flattenAnd (AND p q) = flattenAnd p ++ flattenAnd q
>     flattenAnd p = [p]
>
>     curryList :: [VAL] -> VAL
>     curryList [p] = p
>     curryList (p:ps) = ALL (PRF p) (L (HF "__curry" (\v -> curryList ps))) 


The |curryArg| function takes a proof of a conjunction |P|, and produces a spine
of arguments suitable to apply to a proof of type |curryProp P _|.

> curryArg :: VAL -> [Elim VAL]
> curryArg (PAIR a b) = curryArg a ++ curryArg b
> curryArg a = [A a]


The |uncurryProp| function takes a conjunction |P| and a function |f|. It produces
a function that accepts arguments in a curried style (as required by |curryProp P _|)
and uncurries them to produce a proof of |P|, which it passes to |f|. Thus
|uncurryProp ((A && B) && (C && D)) f == \ w x y z -> f [[w , x] , [y , z]|.

You are not expected to understand this.

> uncurryProp :: VAL -> (VAL -> VAL) -> VAL
> uncurryProp (AND p q) f = uncurryProp p (\v -> uncurryProp q (f . PAIR v))
> uncurryProp _ f = L (HF "__uncurry" f)



The |propSimplify| command takes a proposition and attempts to simplify it. At the
moment it only requires a name supply, but it really should take a context as well.

> propSimplify :: (NameSupplier m) => VAL -> m Simplify

Simplifying |TT| and |FF| is remarkably easy.

> propSimplify ABSURD     = return (SimplifyAbsurd idVAL)
> propSimplify TRIVIAL    = return (SimplifyTrivial VOID)

To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify (AND p q)  = do
>   pSimp <- propSimplify p
>   qSimp <- propSimplify q
>   return (simplifyAnd pSimp qSimp)

To simplify an implication, we do lots of slightly dubious magic.

> propSimplify (ALL (PRF r) s@(L sc)) = do
>   simp <- propSimplify r
>   case simp of
>     SimplifyAbsurd prf -> return (SimplifyTrivial
>         (L (HF "__r" (\rv -> nEOp @@ [prf $$ A rv, PRF (s $$ A rv)]))))
>
>     SimplifyTrivial prfR -> do
>         let s' = s $$ A VOID
>         simp <- propSimplify s'
>         let SimplifyTo t prfTS prfST = forceSimplify s' simp
>         return (makeSimplify t
>                 (L (HF "__t" (\tv -> L (K (prfTS $$ A tv)))))
>                 (L (HF "__rtos" (\rtosv -> prfST $$ A (rtosv $$ A prfR)))))
>
>     SimplifyTo q prfQR prfRQ -> freshRef ("__propSimp" :<: PRF r) (\ref -> do
>         let s' = s $$ A (NP ref)
>         simp <- propSimplify s'
>         case simp of
>             SimplifyAbsurd prf -> return (SimplifyTo (curryProp q ABSURD)
>                 (L (HF "__qsv" (\qsv ->
>                     L (HF "__r" (\r ->
>                         magic (PRF (s $$ A r)) $$ A
>                             (foldl ($$) qsv (curryArg (prfRQ $$ A r))))))))
>                 (L (HF "__rtos" (\rtosv ->
>                     uncurryProp q (\qv -> prf $$ A (rtosv $$ A (prfQR $$ A qv)))))))
>             _ -> return (SimplifyNone (ALL (PRF r) s))
>       )
>
>     _ -> return (SimplifyNone (ALL (PRF r) s))

If nothing matches, we are unable to simplify this term.

> propSimplify tm = return (SimplifyNone tm)


The |simplifyAnd| function takes the results of simplifying two conjuncts and
returns a simplified conjunction.

> simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

> simplifyAnd (SimplifyAbsurd prf) _ =
>     SimplifyAbsurd (L (HF "__absurd" (\pq -> prf $$ A (pq $$ Fst))))

> simplifyAnd _ (SimplifyAbsurd prf) =
>     SimplifyAbsurd (L (HF "__absurd" (\pq -> prf $$ A (pq $$ Snd))))
         
If both propositions are trivial, then their conjunction is trivial:

> simplifyAnd (SimplifyTrivial prfP) (SimplifyTrivial prfQ) =
>     SimplifyTrivial (PAIR prfP prfQ)

If one of them is trivial, then we can simplify to the other:

> simplifyAnd (SimplifyTrivial prfP) (SimplifyNone q) =
>     SimplifyTo q  (L (HF "__q" (\qv -> PAIR prfP qv)))
>                   (L (HF "__pq" (\pqv -> pqv $$ Snd)))

> simplifyAnd (SimplifyTrivial prfP) (SimplifyTo s prfSQ prfQS) =
>     SimplifyTo s  (L (HF "__s" (\sv -> PAIR prfP (prfSQ $$ A sv))))
>                   (L (HF "__pq" (\pqv -> prfQS $$ A (pqv $$ Snd))))

> simplifyAnd (SimplifyNone p) (SimplifyTrivial prfQ) =
>     SimplifyTo p  (L (HF "__p" (\pv -> PAIR pv prfQ)))
>                   (L (HF "__pq" (\pqv -> pqv $$ Fst)))

> simplifyAnd (SimplifyTo r prfRP prfPR) (SimplifyTrivial prfQ) =
>     SimplifyTo r  (L (HF "__r" (\rv -> PAIR (prfRP $$ A rv) prfQ)))
>                   (L (HF "__pq" (\pqv -> prfPR $$ A (pqv $$ Fst))))

If one or both of them simplifies, we can simplify the conjunction:

> simplifyAnd (SimplifyTo r prfRP prfPR) (SimplifyNone q) =
>         SimplifyTo (AND r q)
>             (L (HF "__rq" (\rqv ->
>                 PAIR (prfRP $$ A (rqv $$ Fst)) (rqv $$ Snd))))
>             (L (HF "__pq" (\pqv ->
>                 PAIR (prfPR $$ A (pqv $$ Fst)) (pqv $$ Snd))))

> simplifyAnd (SimplifyNone p) (SimplifyTo s prfSP prfPS) =
>         SimplifyTo (AND p s)
>             (L (HF "__ps" (\psv ->
>                 PAIR (psv $$ Fst) (prfSP $$ A (psv $$ Snd)))))
>             (L (HF "__pq" (\pqv ->
>                 PAIR (pqv $$ Fst) (prfPS $$ A (pqv $$ Snd)))))

> simplifyAnd (SimplifyTo r prfRP prfPR) (SimplifyTo s prfSQ prfQS) =
>         SimplifyTo (AND r s)
>             (L (HF "__rs" (\rs ->
>                 PAIR (prfRP $$ A (rs $$ Fst)) (prfSQ $$ A (rs $$ Snd)))))
>             (L (HF "__pq" (\pq ->
>                 PAIR (prfPR $$ A (pq $$ Fst)) (prfQS $$ A (pq $$ Snd)))))

> simplifyAnd (SimplifyNone p) (SimplifyNone q) = SimplifyNone (AND p q)




> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >> return "Simplified.")
>       "simplify - applies propositional simplification to the current goal."