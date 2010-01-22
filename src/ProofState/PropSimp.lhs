%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs #-}

> module ProofState.PropSimp where

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
where $\Gamma = \{q_i\}_i$, represented by |Right (... :< (q_i, g_i) :< ... , h)|.
\end{itemize}

> type Simplify = Either (VAL -> VAL) (Bwd (REF, VAL -> VAL), VAL)

> simplifyNone :: (NameSupplier m) => VAL -> m Simplify
> simplifyNone p = freshRef ("__p" :<: PRF p) (\ref ->
>     return (Simply (B0 :< (ref, id)) (pval ref)))

> pattern Simply qgs h       = Right (qgs, h)
> pattern SimplyAbsurd prf   = Left prf
> pattern SimplyTrivial prf  = Simply B0 prf


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

<             proofTrace . unlines $ ["Simplified to TRIVIAL with proof",
<                                        show (prf VOID)]
<             prf' <- bquoteHere (prf VOID)
<             proofTrace . unlines $ ["which bquotes to", show prf']

>             let equiv = coe @@ [PRF TRIVIAL, PRF p,
>                                    CON (PAIR (L (K prf)) (L (K VOID))), VOID]
>             equiv' <- bquoteHere equiv
>             give equiv'
>             return ()

>         SimplyAbsurd _ -> throwError' "propSimplifyHere: oh no, goal is absurd!"

>         Simply qgs h -> do
>             let qs = fmap fst qgs
>             proofTrace ("qs: " ++ show qs)

>             qrs <- mapM (\(_ := DECL :<: q) -> do
>                 q' <- bquoteHere q
>                 x <- pickName "q" ""
>                 proofTrace ("subgoal " ++ x ++ ": " ++ show q')
>                 qr <- make (x :<: q')
>                 return (A (evTm qr))
>               ) qs

>             h' <- bquote qs h
>             let lh = wrapLambdas qs h'
>             let pPrf = foldl ($$) (evTm lh) qrs
>             pPrf' <- bquoteHere pPrf

>             proofTrace ("lh: " ++ show lh)

>             giveNext pPrf'
>             return ()

<             let qConjunction = foldr1 AND . fmap (\(_ := DECL :<: ty, _) -> ty) $ qgs
<             let conjunctionProof = foldr1 PAIR qrs

<             let equiv = coe @@ [PRF qConjunction, PRF p,
<                          CON (PAIR (L (HF "__prfQP" prfQP)) (L (HF "__prfPQ" prfPQ))),
<                          conjunctionProof]

<             proofTrace . unlines $ ["Simplified to", show q, "with Q => P by",
<                                     show prfQP, "and P => Q by", show prfPQ,
<                                     "yielding equivalence", show equiv]

<             equiv' <- bquoteHere equiv

<             prfQP' <- bquoteHere prfQP
<             prfPQ' <- bquoteHere prfPQ
<             proofTrace . unlines $ ["(BQ) Simplified to", show q', "with Q => P by",
<                                     show prfQP', "and P => Q by", show prfPQ',
<                                     "yielding equivalence", show equiv']
                 

> dischargeLots :: (NameSupplier m) => Bwd REF -> VAL -> m VAL
> dischargeLots bs v = do
>     v' <- bquote bs v
>     return (evTm (wrapLambdas bs v'))

> wrapLambdas :: Bwd REF -> INTM -> INTM
> wrapLambdas B0 tm = tm
> wrapLambdas (bs :< (n := _)) tm = wrapLambdas bs (L (fst (last n) :. tm))


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


> dischargeRefAll :: (NameSupplier m) => REF -> REF -> m REF
> dischargeRefAll ref (n := DECL :<: PRF ty) = do
>     ty' <- discharge ref ty
>     return (n := DECL :<: PRF (ALL (pty ref) ty'))
> dischargeRefAll ref (n := DECL :<: ty) = do
>     ty' <- discharge ref ty
>     return (n := DECL :<: PRF (ALL (pty ref) ty'))

The |propSimplify| command takes a proposition and attempts to simplify it. At the
moment it only requires a name supply, but it really should take a context as well.

> propSimplify :: (NameSupplier m) => Bwd REF -> VAL -> m Simplify

Simplifying |TT| and |FF| is remarkably easy.

> propSimplify _ ABSURD   = return (SimplyAbsurd   id)
> propSimplify _ TRIVIAL  = return (SimplyTrivial  VOID)

To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify delta (AND p1 p2) = forkNSupply "__propSimp" (propSimplify delta p1)
>     (\ p1Simp -> forkNSupply "__propSimp" (propSimplify delta p2)
>         (\ p2Simp ->
>             return (simplifyAnd p1Simp p2Simp)))



> propSimplify delta p@(ALL (PRF r) s@(L sc)) = do
>     simpR <- propSimplify delta r
>     case simpR of
>         SimplyAbsurd prf -> return (SimplyTrivial
>             (L (HF "__r" (\r -> magic (PRF (s $$ A r)) (prf r)))))

>         _ -> simplifyNone p


To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder. If |t| is absurd, then |p|
simplifies to |(x : s) => FF|. If |t| is trivial, then |p| is trivial. Otherwise,
|p| simplifies to a conjunction of propositions |(x : s) => q| for each |q| in
the simplification of |t|.

> propSimplify delta p@(ALL s l@(L sc)) = freshRef (fortran l :<: s) (\refS -> do
>     simpL <- propSimplify (delta :< refS) (l $$ A (NP refS))
>     case simpL of
>         SimplyAbsurd prf -> freshRef ("__psA" :<: PRF (ALL s (LK ABSURD))) (\refA ->
>             return (Simply (B0 :< (refA,
>                     (\pv -> magic (PRF (ALL s ABSURD)) (prf (pv $$ A (NP refS))))))
>                 (L (HF "__s" (\sv -> magic (PRF (l $$ A sv)) (pval refA $$ A sv))))))
>         SimplyTrivial prf -> do
>             prf' <- discharge refS prf
>             return (SimplyTrivial prf')
>         Simply qgs h -> do
>             h' <- dischargeLots (fmap fst qgs) h
>             qgs' <- mapM (\ (q, g) -> dischargeRefAll refS q
>                 >>= (\ q' -> return (q', (\pv -> (L (HF "__s" (\sv -> g (pv $$ A sv)))))))) qgs
>             let h'' = foldl ($$) h' (fmap (\(q,g) -> (A (NP q $$ A (NP refS)))) qgs')
>             h''' <- discharge refS h''
>             return (Simply qgs' h''')
>             
>   )


If nothing matches, we are unable to simplify this term.

> propSimplify _ tm = simplifyNone tm


The |simplifyAnd| function takes the results of simplifying two conjuncts and
returns a simplified conjunction.

> simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

> simplifyAnd (SimplyAbsurd prf) _ = SimplyAbsurd (prf . ($$ Fst))
> simplifyAnd _ (SimplyAbsurd prf) = SimplyAbsurd (prf . ($$ Snd))
         
Otherwise, we can simplify the conjunction:

> simplifyAnd (Simply qg1s h1) (Simply qg2s h2) =
>     Simply ((fmap (\(q, g) -> (q, g . ($$ Fst))) qg1s) <+>
>         (fmap (\(q, g) -> (q, g . ($$ Snd))) qg2s))
>         (PAIR h1 h2)



> import -> CochonTactics where
>   : nullaryCT "simplify" (propSimplifyHere >> return "Simplified.")
>       "simplify - applies propositional simplification to the current goal."