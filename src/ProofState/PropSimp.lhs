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

> data Simplify  =  SimplifyTo  {  propP :: VAL
>                               ,  propQ :: VAL
>                               ,  proofQP :: VAL -> VAL
>                               ,  proofPQ :: VAL -> VAL
>                               }

> simplifyNone p          = SimplifyTo p p id id
> simplifyAbsurd p prf    = SimplifyTo p ABSURD (magic (PRF p)) prf 
> simplifyTrivial p prfP  = SimplifyTo p TRIVIAL prfP (const VOID)

> pattern SimplyAbsurd   p prf   r = SimplifyTo p ABSURD r prf
> pattern SimplyTrivial  p prfP  r = SimplifyTo p TRIVIAL prfP r

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
>         SimplyTrivial _ prf _ -> do

<             proofTrace . unlines $ ["Simplified to TRIVIAL with proof",
<                                        show (prf VOID)]
<             prf' <- bquoteHere (prf VOID)
<             proofTrace . unlines $ ["which bquotes to", show prf']

>             let equiv = coe @@ [PRF TRIVIAL, PRF p,
>                                    CON (PAIR (L (K (prf VOID))) (L (K VOID))), VOID]
>             equiv' <- bquoteHere equiv
>             give equiv'
>             return ()

>         SimplyAbsurd _ _ _ -> throwError' "propSimplifyHere: oh no, goal is absurd!"

>         SimplifyTo _ q prfQP prfPQ -> do
>             qrs <- mapM (\s -> do
>                 s' <- bquoteHere (PRF s)
>                 x <- pickName "q" ""
>                 qr <- make (x :<: s')
>                 return (evTm qr)
>               ) (flattenAnd q)
>             let equiv = coe @@ [PRF q, PRF p,
>                          CON (PAIR (L (HF "__prfQP" prfQP)) (L (HF "__prfPQ" prfPQ))),
>                          proveConjunction q qrs]

<             proofTrace . unlines $ ["Simplified to", show q, "with Q => P by",
<                                     show prfQP, "and P => Q by", show prfPQ,
<                                     "yielding equivalence", show equiv]

>             equiv' <- bquoteHere equiv

<             prfQP' <- bquoteHere prfQP
<             prfPQ' <- bquoteHere prfPQ
<             proofTrace . unlines $ ["(BQ) Simplified to", show q', "with Q => P by",
<                                     show prfQP', "and P => Q by", show prfPQ',
<                                     "yielding equivalence", show equiv']

>             giveNext equiv'
>             return ()
                 
   
The |flattenAnd| function takes a conjunction and splits it into a list of conjuncts.

> flattenAnd :: VAL -> [VAL]
> flattenAnd (AND p q) = flattenAnd p ++ flattenAnd q
> flattenAnd p = [p]


The |proveConjunction| function takes a conjunction and a list of proofs of its
conjuncts, and produces a proof of the conjunction.

> proveConjunction :: VAL -> [VAL] -> VAL
> proveConjunction p qrs = r
>   where
>     (r, []) = help p qrs
>
>     help :: VAL -> [VAL] -> (VAL, [VAL])
>     help (AND p q) qrs = let
>         (x, qrs')   = help p qrs
>         (y, qrs'')  = help q qrs'
>       in (PAIR x y, qrs'')
>     help _ (qr:qrs) = (qr, qrs)

The |curryProp| function takes a conjunction and a consequent, and produces a
curried proposition that has the pieces of the conjunction as individual
antecedents, followed by the given consequent. Thus
|curryProp (A && B && C) D == (A => B => C => D)|.

> curryProp :: VAL -> VAL -> VAL
> curryProp ps q = curryList $ flattenAnd (AND ps q)
>   where
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


The |magic ty| function takes a proof of |FF| and yields a value of type |ty|.

> magic :: TY -> VAL -> VAL
> magic ty no = nEOp @@ [no, ty]


The |propSimplify| command takes a proposition and attempts to simplify it. At the
moment it only requires a name supply, but it really should take a context as well.

> propSimplify :: (NameSupplier m) => VAL -> m Simplify

Simplifying |TT| and |FF| is remarkably easy.

> propSimplify ABSURD     = return (simplifyAbsurd   ABSURD   id)
> propSimplify TRIVIAL    = return (simplifyTrivial  TRIVIAL  id)

To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify (AND p q)  = do
>   pSimp <- propSimplify p
>   qSimp <- propSimplify q
>   return (simplifyAnd pSimp qSimp)

To simplify an implication, we do lots of slightly dubious magic.

> propSimplify p@(ALL (PRF r) s@(L sc)) = do
>   simpR <- propSimplify r
>   case simpR of
>     SimplyAbsurd _ prf _ -> return (simplifyTrivial p
>         (const (L (HF "__r" (\rv -> nEOp @@ [prf rv, PRF (s $$ A rv)])))))
>
>     _ ->  freshRef ("__propSimp" :<: PRF r) (\ref -> do
>         let s' = s $$ A (NP ref)
>         simpS <- propSimplify s'
>         case (simpR, simpS) of
>             (SimplyTrivial _ prfR _, SimplifyTo _ t prfTS prfST) -> 
>                 return (SimplifyTo p t
>                     (\tv -> L (K (prfTS tv)))
>                     (\pv -> prfST (prfR pv)))
>
>             (SimplifyTo _ q prfQR prfRQ, SimplyAbsurd _ prf _) -> return (SimplifyTo
>                     p
>                     (curryProp q ABSURD)
>                     (\qsv ->
>                         L (HF "__r" (\r ->
>                             magic (PRF (s $$ A r))
>                                 (foldl ($$) qsv (curryArg (prfRQ r))))))
>                     (\pv ->
>                       uncurryProp q (\qv -> prf (pv $$ A (prfQR qv)))))
>
>             (_, SimplyTrivial _ prfS _) -> return (simplifyTrivial p (const (L (K (prfS VOID)))))
>
>             _ -> return (simplifyNone p)
>       )

> propSimplify p@(EQBLUE (sty :>: s) (tty :>: t))
>   | not (isNeutral s || isNeutral t) = return (SimplifyTo p
>         (eqGreen @@ [sty, s, tty, t])
>         (\egv -> CON egv)
>         (\ebv -> ebv $$ Out))
>   where
>     isNeutral :: VAL -> Bool
>     isNeutral (N _)  = True
>     isNeutral _      = False

If nothing matches, we are unable to simplify this term.

> propSimplify tm = return (simplifyNone tm)


The |simplifyAnd| function takes the results of simplifying two conjuncts and
returns a simplified conjunction.

> simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

> simplifyAnd (SimplyAbsurd p prf _) (SimplifyTo q _ _ _) =
>     simplifyAbsurd (AND p q) (\pq -> prf (pq $$ Fst))

> simplifyAnd (SimplifyTo p _ _ _) (SimplyAbsurd q prf _) =
>     simplifyAbsurd (AND p q) (\pq -> prf (pq $$ Snd))
         
If one of them is trivial, then we can simplify to the other:

> simplifyAnd (SimplyTrivial p prfP _) (SimplifyTo q s prfSQ prfQS) =
>     SimplifyTo (AND p q) s
>         (\sv -> PAIR (prfP VOID) (prfSQ sv))
>         (\pqv -> prfQS (pqv $$ Snd))

> simplifyAnd (SimplifyTo p r prfRP prfPR) (SimplyTrivial q prfQ _) =
>     SimplifyTo (AND p q) r
>         (\rv -> PAIR (prfRP rv) (prfQ VOID))
>         (\pqv -> prfPR (pqv $$ Fst))

If one or both of them simplifies, we can simplify the conjunction:

> simplifyAnd (SimplifyTo p r prfRP prfPR) (SimplifyTo q s prfSQ prfQS) =
>         SimplifyTo (AND p q) (AND r s)
>             (\rs -> PAIR (prfRP (rs $$ Fst)) (prfSQ (rs $$ Snd)))
>             (\pq -> PAIR (prfPR (pq $$ Fst)) (prfQS (pq $$ Snd)))




> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >> return "Simplified.")
>       "simplify - applies propositional simplification to the current goal."