\newcommand{\simpto}{\leadsto}
\newcommand{\and}{\wedge}
\newcommand{\conj}[2]{\bigwedge_{#2} \vec{{#1}_{#2}}}
\newcommand{\BlueEq}[4]{(\Bhab{#2}{#1}) \EQ (\Bhab{#4}{#3})}
\newcommand{\GreenEq}[4]{(\Bhab{#2}{#1}) \green{\leftrightarrow} (\Bhab{#4}{#3})}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances,
>              PatternGuards, TupleSections #-}

> module Tactics.PropositionSimplify where

> import Prelude hiding (any, foldl)

> import Control.Applicative 
> import Control.Monad.Reader

> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.ProofKit
> import ProofState.Interface.Lifting
> import ProofState.Interface.Name
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving

%endif

\section{Propositional Simplification}

We need a proper logging system!

> simpTrace :: String -> ProofState ()
> simpTrace s = return ()

\subsection{Setting the Scene}

A \emph{simple proposition}\index{simple proposition} is either
$\Absurd$ or a (possibly trivial) conjunction, where each conjunct is:
\begin{itemize}
\item a neutral term of type $\Prop$;
\item a blue equation with (at least) one neutral side;
\item $\ALL{x}{S} P$, with $S$ not a proof and $P$ simple; or
\item $P \Imply Q$, with $P$ and $Q$ simple and $P$ not $\Absurd$.
\end{itemize}

We write $\Gamma \Tn P \simpto R$ to mean that the proposition $P$ in context
$\Gamma$ simplifies to the simple proposition $R$. The rules in
Figure~\ref{fig:Tactics.PropositionSimplify.rules}
define this judgment, and the implementation follows these rules.

\begin{figure}[ht]

$$
\CAxiom{\Gamma \Tn \Trivial \simpto \Trivial}
\qquad
\CAxiom{\Gamma \Tn \Absurd \simpto \Absurd}
$$

$$
\Rule{\Gamma \Tn P \simpto \Absurd}
     {\Gamma \Tn P \and Q \simpto \Absurd}
\qquad
\Rule{\Gamma \Tn Q \simpto \Absurd}
     {\Gamma \Tn P \and Q \simpto \Absurd}
\qquad
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad  \Gamma \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn P \and Q \simpto \conj{P}{i} \and \conj{Q}{j}}
$$

$$
\Rule{\Gamma \Tn P \simpto \Absurd}
     {\Gamma \Tn P \Imply Q \simpto \Trivial}
\qquad
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad
      \Gamma, \vec{P_i} \Tn Q \simpto \Trivial}
     {\Gamma \Tn P \Imply Q \simpto \Trivial}
\qquad
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad
      \Gamma, \vec{P_i} \Tn Q \simpto \Absurd}
     {\Gamma \Tn P \Imply Q \simpto \vec{P_i} \Imply \Absurd}
$$

$$
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad
      \Gamma, \vec{P_i} \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn P \Imply Q \simpto \vec{P_i} \Imply (\conj{Q}{j})}
$$

$$
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \Absurd}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \ALL{x}{S} \Absurd}
\qquad
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \Trivial}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \Trivial}
\qquad
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \ALL{x}{S} (\conj{Q}{j})}
$$

$$
\CAxiom{\Gamma \Tn \BlueEq{S}{s}{S}{s} \simpto \Trivial}
\qquad
\Rule{\Gamma \Tn \GreenEq{S}{s}{T}{t} \simpto R}
     {\Gamma \Tn \BlueEq{S}{s}{T}{t} \simpto R}
\qquad
\Rule{\Gamma \Vdash P}
     {\Gamma \Tn P \simpto \Trivial}
$$

\caption{Propositional simplification rules}
\label{fig:Tactics.PropositionSimplify.rules}
\end{figure}


Given $\Gamma \vdash \Bhab{P}{\Prop}$, the propositional simplifier will either:
\begin{itemize}

\item discover that $P$ is absurd and provide a proof
$\Gamma \vdash \Bhab{f}{(\prf{P} \Imply \Absurd)}$,
represented by |Left f|; or

\item simplify $P$ to a conjunction $\conj{P}{i}$ together with
proofs $\Gamma \vdash \Bhab{g_i}{(\prf{P} \Imply P_i)}$ and
$\Gamma, \vec{P_i} \vdash \Bhab{h}{(\prf{P})}$,
represented by |Right (ps, gs, h)|.

\end{itemize}

> type Simplify = Either (VAL -> VAL) (Bwd REF, Bwd VAL, VAL)

> pattern Simply ps gs h     = Right (ps, gs, h)
> pattern SimplyAbsurd prf   = Left prf
> pattern SimplyTrivial prf  = Simply B0 B0 prf
> pattern SimplyOne p g h    = Simply (B0 :< p) (B0 :< g) h


> type Simplifier x = ReaderT NameSupply Maybe x
                 

\question{Move the following to somewhere more sensible.}

The |magic ty| function takes a proof of |Absurd| and yields a value
of type |ty|.

> magic :: TY -> VAL -> VAL
> magic ty no = nEOp @@ [no, ty]


The |...| operator is composition of |VAL| functions.

> (...) :: VAL -> VAL -> VAL
> f ... g = L (HF "xc" (\x -> f $$ A (g $$ A x)))

The curiously more useful |..!| operator is composition of a genuine |VAL|
function with a |VAL -> VAL| function.

> (..!) :: VAL -> (VAL -> VAL) -> VAL
> f ..! g = L (HF "xc2" (\x -> f $$ A (g x)))


\subsection{Simplification in Action}

The |propSimplify| command takes a proposition and attempts to simplify it.

> propSimplify :: Bwd REF -> Bwd REF -> VAL -> Simplifier Simplify


Simplifying |TT| and |FF| is remarkably easy.

> propSimplify _ _ ABSURD   = return (SimplyAbsurd   id)
> propSimplify _ _ TRIVIAL  = return (SimplyTrivial  VOID)


To simplify a conjunction, we simplify each conjunct separately, then call the
|simplifyAnd| helper function to combine the results.

> propSimplify gamma delta (AND p1 p2) = forkNSupply "psAnd1"
>     (forceSimplify gamma delta p1)
>     (\ (p1Simp, _) -> forkNSupply "psAnd2"
>         (forceSimplify gamma delta p2)
>         (\ (p2Simp, _) -> return (simplifyAnd p1Simp p2Simp)))
>   where
>     simplifyAnd :: Simplify -> Simplify -> Simplify

If either |p| or |q| is absurd, then we can easily show that |p && q| is absurd:

>     simplifyAnd (SimplyAbsurd prf) _ = SimplyAbsurd (prf . ($$ Fst))
>     simplifyAnd _ (SimplyAbsurd prf) = SimplyAbsurd (prf . ($$ Snd))
         
Otherwise, we can simplify the conjunction, post-composing the proofs with
the application of |Fst| or |Snd| as appropriate.

>     simplifyAnd (Simply q1s g1s h1) (Simply q2s g2s h2) =
>         Simply  (q1s <+> q2s)
>                 (fmap (..! ($$ Fst)) g1s <+> (fmap (..! ($$ Snd)) g2s))
>                 (PAIR h1 h2)



To simplify |p = x : (:- s) => l|, we first try to simplify |s|:

> propSimplify gamma delta p@(ALL (PRF s) l) =
>     forkNSupply  "psImp1" 
>                  (forceSimplifyNamed gamma delta s (fortran l))
>                  antecedent
>   where
>     antecedent :: (Simplify, Bool) -> Simplifier Simplify

If |s| is absurd then |p| is trivial, which we can prove by doing |magic|
whenever someone gives us an element of |s|.

>     antecedent (SimplyAbsurd prfAbsurdS, _) =
>       return $ SimplyTrivial $ L . HF "antecedentAbsurd" $ \sv ->
>                                magic (PRF (l $$ A sv)) (prfAbsurdS sv)

If |s| is trivial, then we go under the binder by applying the proof,
and then simplify |l|. Then |p| simplifies to the result of
simplifying |l|, with the proofs constructed by $\lambda$-abstracting
in one direction and applying the proof of |s| in the other direction.

>     antecedent (SimplyTrivial prfS, _) =
>         forkNSupply  "psImp2" 
>                      (forceSimplify gamma delta (l $$ A prfS)) 
>                      (consequentTrivial . fst)
>       where
>         consequentTrivial :: Simplify -> Simplifier Simplify
>         consequentTrivial (SimplyAbsurd prfAbsurdT) =
>             return $ SimplyAbsurd (prfAbsurdT . ($$ A prfS))
>         consequentTrivial (SimplyTrivial prfT)  = 
>             return $ SimplyTrivial (LK prfT)
>         consequentTrivial (Simply tqs tgs th)   = 
>             return $ Simply  tqs
>                              (fmap (..! ($$ A prfS)) tgs)
>                              (LK th)

If |s| simplifies nontrivially, we have a bit more work to do. We simplify |t|
under the binder by adding the simplified conjuncts of |s| to the context and
applying |l| to |sh| (the proof of |s| in the extended context). 

>     antecedent (Simply sqs sgs sh, didSimplifyAntecedent) =
>         forkNSupply  "psImp3" 
>                      (forceSimplify gamma (delta <+> sqs) (l $$ A sh)) 
>                      consequent
>       where
>         consequent :: (Simplify, Bool) -> Simplifier Simplify
>         consequent (SimplyAbsurd prfAbsurdT, _) = do
>             madness <- dischargeAllLots sqs (PRF ABSURD)
>             freshRef ("madness" :<: madness) $ \ref -> 
>               freshRef ("pref" :<: p) $ \pref -> do
>                 g <- dischargeLots sqs (prfAbsurdT (NP pref $$ A sh))
>                 g' <- discharge pref g
>                 return $ 
>                   SimplyOne ref
>                             (L . HF "p" $ \pv -> g' $$ A pv)
>                             (L . HF "consequentAbsurd" $ \sv -> 
>                                 magic (PRF (l $$ A sv))
>                                       (NP ref $$$ (fmap (A . ($$ A sv)) sgs)))

If the consequent |t| is trivial, then the implication is trivial, which we can
prove as follows:
\begin{enumerate}
\item Discharge the proof of |t| over the conjuncts |sqs| to get a
      $\lambda$-lifted proof |prfT'|.
\item Construct a proof of |(x :\!\!- s) => t| that takes a proof of
      |s| and applies the proofs |sgs| to get proofs of the |sqs|, which can
      then be passed to |prfT'| to get a proof of |t|.
\end{enumerate}

>         consequent (SimplyTrivial prfT, _) = do
>             prfT' <- dischargeLots sqs prfT
>             return $ SimplyTrivial $ 
>                      L . HF "consequentTrivial" $ \sv ->
>                          prfT' $$$ (fmap (A . ($$ A sv)) sgs)

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

>         consequent (Simply tqs tgs th, didSimplifyConsequent) 
>           | didSimplifyAntecedent || didSimplifyConsequent = do
>             pqs <- Data.Traversable.mapM (dischargeRefAlls sqs) tqs
>             pgs <- Data.Traversable.mapM wrapper tgs
>
>             freshRef ("sref" :<: PRF s) $ \sref -> do
>                 th1 <- dischargeLots tqs th
>                 let  sgSpine  = fmap (\sg -> A (sg $$ A (NP sref))) sgs
>                      th2      = th1 $$$ fmap (\pq -> A (NP pq $$$ sgSpine)) pqs
>                 th3 <- dischargeLots sqs th2
>                 let th4 = th3 $$$ sgSpine
>                 ph <- discharge sref th4
>                 return $ Simply pqs pgs ph
>
>           where
>             wrapper :: (NameSupplier m) => VAL -> m VAL
>             wrapper tg = freshRef ("pref" :<: p) $ \pref -> do
>                 pg <- dischargeLots sqs (tg $$ A (NP pref $$ A sh))
>                 discharge pref pg

If we get to this point, neither the antecedent nor the consequent simplified,
so we had better give up.

>         consequent _ = (|) 

To simplify a proposition that is universally quantified over a (completely
canonical) enumeration, we can simplify it for each possible value.

> propSimplify gamma delta p@(ALL (ENUMT e) b) | Just ts <- getTags B0 e = 
>     process B0 B0 B0 ZE ts
>   where
>     getTags :: Bwd VAL -> VAL -> Maybe (Bwd VAL)
>     getTags ts NILE         = (| ts |)
>     getTags ts (CONSE t e)  = getTags (ts :< t) e
>     getTags ts _            = (|)
>
>     process :: Bwd REF -> Bwd VAL -> Bwd VAL -> VAL -> Bwd VAL
>         -> Simplifier Simplify
>     process qs gs hs n B0 = return $ Simply qs gs $ L $ HF "xe" $ \ x ->
>         switchOp @@ [e, x, L (HF "yb" $ \ y -> PRF (b $$ A y)),
>                          Prelude.foldr PAIR VOID (trail hs)]
>     process qs1 gs1 hs1 n (ts :< t) = forkNSupply "psEnumImp"
>         (forceSimplify gamma delta (b $$ A n)) $
>         \ (btSimp, _) -> case btSimp of
>             SimplyAbsurd prf  -> return $ SimplyAbsurd (\ v -> prf (v $$ A n))
>             Simply qs2 gs2 h2  -> do
>                 let gs2' = fmap (..! ($$ A n)) gs2
>                 process (qs1 <+> qs2) (gs1 <+> gs2') (hs1 :< h2) (SU n) ts


To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder.

> propSimplify gamma delta p@(ALL s l) = 
>     freshRef (fortran l :<: s) $ \refS -> 
>       forkNSupply  "psAll" 
>           (propSimplify gamma (delta :< refS) (l $$ A (NP refS))) 
>           (thingy refS)
>   where
>     thingy :: (NameSupplier m) => REF -> Simplify -> m Simplify

If |t| is absurd, then |p| simplifies to |(x : s) => FF|. 

>     thingy refS (SimplyAbsurd prf) =
>       freshRef ("psA" :<: PRF (ALL s (LK ABSURD))) $ \refA -> 
>         return $
>           SimplyOne  refA
>                      (L . HF "p" $ \pv -> 
>                       magic  (PRF (ALL s (LK ABSURD))) 
>                              (prf (pv $$ A (NP refS))))
>                      (L . HF "consequentAbsurd2" $ \sv -> 
>                       magic  (PRF (l $$ A sv)) 
>                              (pval refA $$ A sv))

If |t| is trivial, then |p| is trivial.

>     thingy refS (SimplyTrivial prf) = do
>         prf' <- discharge refS prf
>         return $ SimplyTrivial prf'

Otherwise, |p| simplifies to a conjunction of propositions |(x : s) =>
q| for each |q| in the simplification of |t|.

>     thingy refS (Simply qs gs h) = do
>         pqs <- Data.Traversable.mapM (dischargeRefAlls (B0 :< refS)) qs
>         let pgs = fmap wrapper gs
>         h1 <- dischargeLots qs h
>         let h2 = h1 $$$ fmap (\q -> A (NP q $$ A (NP refS))) pqs
>         ph <- discharge refS h2
>         return (Simply pqs pgs ph)
>       where

The |wrapper| says how to get a proof |pg : p -> pq| given a proof |g : t -> q|.
Since |pq == (x : s) => q| we can give back a function that takes proofs
|pv : p| and |sv : s|, applies |pv| to |sv| to give a proof of |t|, then
applies |g| to this proof to get a proof of |q|.

>         wrapper :: VAL -> VAL
>         wrapper g = L . HF "p" $ \pv ->
>                     L . HF "s" $ \sv ->
>                     g $$ A (pv $$ A sv)


To simplify a blue equation, we use |simplifyBlue|.

> propSimplify gamma delta (EQBLUE (sty :>: s) (tty :>: t)) = 
>     simplifyBlue True gamma delta (sty :>: s) (tty :>: t)


To simplify a green equation, we cannot unroll the corresponding blue
equation because we would get infinite loops, but we can use the other
simplifications for blue equations. If we do not find a proof, we
return the blue version as the simplification result because it is
nicer than a green equation for the user.

> propSimplify gamma delta p@(N (op :@ [sty, s, tty, t]))
>   | op == eqGreen = do
>       m <- optional $ simplifyBlue False gamma delta (sty :>: s) (tty :>: t)
>       case m of
>           Just (SimplyTrivial prf) -> return $ SimplyTrivial (prf $$ Out)
>           Nothing -> do
>              freshRef ("q" :<: PRF (EQBLUE (sty :>: s) (tty :>: t))) $ \qRef ->
>                return $ SimplyOne  qRef
>                                    (L . HF "p" $ CON)
>                                    (NP qRef $$ Out)


If nothing matches, we can always try searching the context.

> propSimplify gamma delta p = propSearch gamma delta p


The |simplifyBlue| command attempts to simplify a blue equation using
refl, optionally unrolling it (calling eqGreen and simplifying the
resulting pieces), or just searching the context.

> simplifyBlue ::  Bool -> Bwd REF -> Bwd REF -> TY :>: VAL
>                  -> TY :>: VAL -> Simplifier Simplify 
> simplifyBlue canUnroll gamma delta (sty :>: s) (tty :>: t) = 
>     useRefl
>     <|> unroll canUnroll
>     <|> propSearch gamma delta (EQBLUE (sty :>: s) (tty :>: t))
>  where
>    useRefl :: Simplifier Simplify
>    useRefl = do
>        guard =<< (asks . equal $ SET :>: (sty, tty))
>        guard =<< (asks . equal $ sty :>: (s, t))
>        let w = pval refl $$ A sty $$ A s
>        return $ SimplyTrivial w
>
>    unroll :: Bool -> Simplifier Simplify
>    unroll False  = (|)
>    unroll True   = case opRun eqGreen [sty, s, tty, t] of
>        Left _         -> (|)
>        Right TRIVIAL  -> return $ SimplyTrivial (CON VOID)
>        Right q        -> forkNSupply  "psEq"
>                                       (forceSimplify gamma delta q)
>                                       (equality . fst)
>          
>    equality :: Simplify -> Simplifier Simplify
>    equality (SimplyAbsurd prf) = return $ SimplyAbsurd (prf . ($$ Out))
>    equality (Simply qs gs h) = return $ Simply  qs
>                                                 (fmap (..! ($$ Out)) gs)
>                                                 (CON h)




The |propSearch| operation searches the context for a proof of the proposition,
and if it finds one, returns the trivial simplification. When |seekProof| finds
a proof in the context, it calls |backchain| to go under any implications and
test if the consequent matches the goal; if so, |backchain| then calls
|seekProof| to attempt to prove the hypotheses, in the context with the
backchained proposition removed. 

> propSearch :: Bwd REF -> Bwd REF -> VAL -> Simplifier Simplify
> propSearch gamma delta p = do
>   prf <- seekProof (gamma <+> delta) F0 p
>   return $ SimplyTrivial prf
>     where 
>     seekProof :: Bwd REF -> Fwd REF -> VAL -> Simplifier VAL
>     seekProof B0 _ _ = (|)
>     seekProof (rs :< ref@(_ := DECL :<: PRF q)) fs p =
>         backchain (rs :< ref) fs B0 p q <|> seekProof rs (ref :> fs) p
>     seekProof (rs :< ref) fs p = seekProof rs (ref :> fs) p
>  
>     backchain :: Bwd REF -> Fwd REF -> Bwd REF -> VAL -> VAL -> Simplifier VAL
>     backchain rs fs ss p (ALL (PRF s) l) = freshRef ("bc" :<: PRF s) $ \sRef ->
>         backchain rs fs (ss :< sRef) p (l $$ A (NP sRef))
>                                                                       
>     backchain (rs :< ref) fs ss p q = do
>         guard =<< (asks . equal $ PROP :>: (p, q))
>         ssPrfs <- Data.Traversable.mapM (seekProof (rs <>< fs) F0 . unPRF . pty) ss
>         return $ pval ref $$$ fmap A ssPrfs
>
>     unPRF :: VAL -> VAL
>     unPRF (PRF p) = p


As a variant of |propSimplify|, |forceSimplify| guarantees to give a result,
by trying to simplify the proposition and yielding an identical copy if
simplification fails. This is useful in cases such as |&&|, where we know
we can do some simplification even if the conjuncts do not simplify.
It also returns a boolean indicating whether simplification occurred.

The |forceSimplifyNamed| variant takes a name hint that will be
used if simplification fails.

> forceSimplify gamma delta p = forceSimplifyNamed gamma delta p ""

> forceSimplifyNamed :: Bwd REF -> Bwd REF -> VAL -> String ->
>     Simplifier (Simplify, Bool)
> forceSimplifyNamed gamma delta p hint  =
>     (propSimplify gamma delta p >>= return . (, True))
>     <|> simplifyNone hint (PRF p)
>   where
>       simplifyNone :: (NameSupplier m) => String -> TY -> m (Simplify, Bool)
>       simplifyNone hint ty =
>           freshRef (nameHint hint ty :<: ty) $ \ref ->
>               return (SimplyOne ref (idVAL "id") (NP ref), False)
>   
>       nameHint :: String -> VAL -> String
>       nameHint hint _ | not (null hint) = hint
>       nameHint _ (NP (n := _)) = "" ++ fst (last n)
>       nameHint _ (L (HF s _)) = "" ++ s
>       nameHint _ _ = "xnh"



\subsection{Invoking Simplification}

> runPropSimplify :: VAL -> ProofState (Maybe Simplify)
> runPropSimplify p = do
>     nsupply <- askNSupply
>     es <- getParamsInScope
>     return $ runReaderT (propSimplify (bwdList es) B0 p) nsupply

The |propSimplifyHere| command attempts propositional simplification on the
current location, which must be an open goal of type |PRF p| for some |p|.
If it is unable to simplify |p| or simplifies it to |FF|, it will fail and
throw an error. Otherwise, it will create zero or more new subgoals
(from the conjuncts of the simplified proposition, if any), solve the
current goal with the subgoals, and return a list of them.

> propSimplifyHere :: ProofState (Bwd (EXTM :=>: VAL))
> propSimplifyHere = do
>     simpTrace "propSimplifyHere"
>     (_ :=>: PRF p) <- getHoleGoal
>     pSimp <- runPropSimplify p
>     case pSimp of
>         Nothing                   -> throwError' $ err "propSimplifyHere: unable to simplify."
>         Just (SimplyAbsurd _)     -> throwError' $ err "propSimplifyHere: oh no, goal is absurd!"
>
>         Just (SimplyTrivial prf)  -> bquoteHere prf >>= give >> return B0
>
>         Just (Simply qs _ h) -> do
>             qrs  <- Data.Traversable.mapM makeSubgoal qs
>             h'   <- dischargeLots qs h
>             prf  <- bquoteHere (h' $$$ fmap (A . valueOf) qrs)
>             give prf
>             return qrs

The |makeSubgoal| command makes a new subgoal whose type corresponds to the type
of the given reference, and returns its term and value representations.

> makeSubgoal :: REF -> ProofState (EXTM :=>: VAL)
> makeSubgoal ref = do
>     q'  <- bquoteHere (pty ref)
>     x   <- pickName "q" (fst (last (refName ref)))
>     make (x :<: q')


The |propSimplify| tactic attempts to simplify the type of the current goal,
which should be propositional. Usually one will want to use |simplify| instead,
or simplification will happen automatically (with the |let| and |<=| tactics),
but this is left for backwards compatibility.

> import -> CochonTacticsCode where
>     propSimplifyTactic :: ProofState String
>     propSimplifyTactic = do
>         subs <- propSimplifyHere 
>         case subs of
>             B0  -> return "Solved."
>             _   -> do
>                 subStrs <- Data.Traversable.mapM (prettyType . termOf)  subs
>                 nextGoal
>                 return ("Simplified to:\n" ++ 
>                     foldMap (\s -> s ++ "\n") subStrs)
>       where
>         prettyType :: EXTM -> ProofState String
>         prettyType tm = do
>             (_ :<: ty) <- inferHere tm
>             ty' <- bquoteHere ty
>             d <- prettyHere (SET :>: ty')
>             return (renderHouseStyle d)

> import -> CochonTactics where
>   : nullaryCT "propsimplify" propSimplifyTactic
>       "propsimplify - applies propositional simplification to the current goal."