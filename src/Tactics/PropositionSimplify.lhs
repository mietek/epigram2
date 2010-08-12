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
> import Control.Monad.Identity

> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import NameSupply.NameSupply
> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Rules
> import Evidences.Mangler

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

A proposition is \emph{nice} if it is:
\begin{itemize}
\item a neutral term of type $\Prop$;
\item a blue equation with (at least) one neutral side;
\item $\ALL{x}{S} P$, with $S$ not a proof and $P$ nice or $\Absurd$;
\item $P \Imply Q$, with $P$ nice and $Q$ nice or $\Absurd$.
\end{itemize}
A proposition is \emph{simple}\index{simple proposition} if it is $\Absurd$ or
a conjunction of zero or more nice propositions.

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
     {\Gamma \Tn P \Imply Q \simpto \bigwedge_j (\vec{P_i} \Imply Q_j)}
$$

$$
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \Absurd}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \ALL{x}{S} \Absurd}
\qquad
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \Trivial}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \Trivial}
\qquad
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \bigwedge_j (\ALL{x}{S} Q_j)}
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

> type Simplify = Either  (EXTM -> INTM)
>                         (Bwd (REF :<: INTM), Bwd (EXTM -> INTM), INTM)

> pattern Simply ps gs h     = Right (ps, gs, h)
> pattern SimplyAbsurd prf   = Left prf
> pattern SimplyTrivial prf  = Simply B0 B0 prf
> pattern SimplyOne p g h    = Simply (B0 :< p) (B0 :< g) h


> type Simplifier x = ReaderT NameSupply Maybe x
                 

\adam{we should move the following to somewhere more sensible.}

> substitute :: Bwd (REF :<: INTM) -> Bwd INTM -> INTM -> INTM
> substitute bs vs t = substMangle bs vs 0 %% t
>   where
>     substMangle :: Bwd (REF :<: INTM) -> Bwd INTM -> Int -> Mangle Identity REF REF
>     substMangle bs vs i = Mang
>       {  mangP = \ x ies -> (|(help bs vs x i $:$) ies|)
>       ,  mangV = \ i ies -> (|(V i $:$) ies|)
>       ,  mangB = \ _ -> substMangle bs vs (i + 1)
>       }
>     
>     help :: Bwd (REF :<: INTM) -> Bwd INTM -> REF -> Int -> EXTM
>     help B0 B0 x i = P x
>     help (bs :< (y :<: ty)) (vs :< v) x i
>       | x == y     = v ?? ty
>       | otherwise  = help bs vs x i
 



\subsection{Simplification in Action}

The |propSimplify| command takes a global context, local context and proposition;
it attempts to simplify the proposition following the rules above.

> propSimplify :: Bwd REF -> Bwd (REF :<: INTM) -> VAL -> Simplifier Simplify


Simplifying $\Trivial$ and $\Absurd$ is remarkably easy.

> propSimplify _ _ ABSURD   = return (SimplyAbsurd   N)
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

>     simplifyAnd (SimplyAbsurd prf) _ = SimplyAbsurd (prf . (:$ Fst))
>     simplifyAnd _ (SimplyAbsurd prf) = SimplyAbsurd (prf . (:$ Snd))
         
Otherwise, we can simplify the conjunction, pre-composing the proofs with
the application of |Fst| or |Snd| as appropriate.

>     simplifyAnd (Simply q1s g1s h1) (Simply q2s g2s h2) =
>         Simply  (q1s <+> q2s)
>                 (fmap (. (:$ Fst)) g1s <+> (fmap (. (:$ Snd)) g2s))
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

>     antecedent (SimplyAbsurd prfAbsurdS, _) = do
>       l' <- bquote B0 l
>       s' <- bquote B0 s
>       let l'' = l' :? ARR (PRF s') PROP
>       return . SimplyTrivial . L $ "antecedentAbsurd" :.
>           (N (nEOp :@ [prfAbsurdS (V 0), PRF (N (l'' :$ A (NV 0)))]))

If |s| is trivial, then we go under the binder by applying the proof,
and then simplify |l|. Then |p| simplifies to the result of
simplifying |l|, with the proofs constructed by $\lambda$-abstracting
in one direction and applying the proof of |s| in the other direction.

>     antecedent (SimplyTrivial prfS, _) =
>         forkNSupply  "psImp2" 
>                      (forceSimplify gamma delta (l $$ A (evTm prfS)))
>                      (consequentTrivial . fst)
>       where
>         consequentTrivial :: Simplify -> Simplifier Simplify
>         consequentTrivial (SimplyAbsurd prfAbsurdT) =
>             return $ SimplyAbsurd (prfAbsurdT . (:$ A prfS))
>         consequentTrivial (SimplyTrivial prfT)  = 
>             return $ SimplyTrivial (LK prfT)
>         consequentTrivial (Simply tqs tgs th)   = 
>             return $ Simply  tqs
>                              (fmap (. (:$ A prfS)) tgs)
>                              (LK th)

If |s| simplifies nontrivially, we have a bit more work to do. We simplify |t|
under the binder by adding the simplified conjuncts of |s| to the context and
applying |l| to |sh| (the proof of |s| in the extended context). 

>     antecedent (Simply sqs sgs sh, didSimplifyAntecedent) =
>         forkNSupply  "psImp3" 
>                      (forceSimplify gamma (delta <+> sqs) (l $$ A (evTm sh)))
>                      consequent
>       where
>         consequent :: (Simplify, Bool) -> Simplifier Simplify
>         consequent (SimplyAbsurd prfAbsurdT, _) = do
>             let madness = dischargeAllLots' sqs (PRF ABSURD)
>             freshRef ("madness" :<: evTm madness) $ \ madRef ->
>               freshRef ("sRef" :<: s) $ \ sRef -> do
>                 l' <- bquote B0 l
>                 s' <- bquote B0 s
>                 let l'' = l' ?? ARR (PRF s') PROP
>                 let body = N (nEOp :@ [
>                         N (P madRef $## map ($ (P sRef)) (trail sgs)),
>                         PRF (N (l'' :$ A (NP sRef)))
>                       ])
>                 return $ SimplyOne (madRef :<: madness)
>                     (\ pv -> dischargeLots' (fmap fstEx sqs)
>                                             (prfAbsurdT (pv :$ A sh)))
>                     (dischargeLots' (B0 :< sRef) body)


If the consequent |t| is trivial, then the implication is trivial, which we can
prove as follows:
\begin{enumerate}
\item Discharge the proof of |t| over the conjuncts |sqs| to get a
      $\lambda$-lifted proof |prfT'|.
\item Construct a proof of |(x :\!\!- s) => t| that takes a proof of
      |s| and applies the proofs |sgs| to get proofs of the |sqs|, which can
      then be passed to |prfT'| to get a proof of |t|.
\end{enumerate}

>         consequent (SimplyTrivial prfT, _) = 
>             freshRef ("sRef" :<: PRF s) $ \ sRef -> do
>                 let z = substitute sqs (fmap ($ (P sRef)) sgs) prfT
>                 let prf' = dischargeLots' (B0 :< sRef) z
>                 return $ SimplyTrivial prf'

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
>             let pqs = fmap (dischargeRefAlls' sqs) tqs
>             let pgs = fmap wrapper tgs
>             freshRef ("sref" :<: PRF s) $ \ sref -> do
>                 let  squiz  = fmap ($ (P sref)) sgs
>                 let th2 = substitute tqs (fmap (\ (pq :<: _) -> N (P pq $## trail squiz)) pqs) th
>                 let th4 = substitute sqs squiz th2
>                 let ph = dischargeLots' (B0 :< sref) th4
>                 return $ Simply pqs pgs ph

> {-
>                 let th1 = dischargeLots' (fmap fstEx tqs) th
>                 let  sgSpine  = fmap (\sg -> A (sg $$ A (NP sref))) sgs
>                      th2      = th1 $$$ fmap (\pq -> A (NP pq $$$ sgSpine)) pqs
>                 th3 <- dischargeLots sqs th2
>                 let th4 = th3 $$$ sgSpine
>                 ph <- discharge sref th4
>                 return $ Simply pqs pgs ph
> -}
>
>           where
>             wrapper :: (EXTM -> INTM) -> EXTM -> INTM
>             wrapper tg p = dischargeLots' (fmap fstEx sqs) (tg (p :$ A sh))


If we get to this point, neither the antecedent nor the consequent simplified,
so we had better give up.

>         consequent _ = (|) 


To simplify a proposition that is universally quantified over a (completely
canonical) enumeration, we can simplify it for each possible value.

> propSimplify gamma delta p@(ALL (ENUMT e) b) | Just ts <- getTags B0 e = 
>     process B0 B0 B0 (ZE :=>: ZE) ts
>   where
>     getTags :: Bwd VAL -> VAL -> Maybe (Bwd VAL)
>     getTags ts NILE         = (| ts |)
>     getTags ts (CONSE t e)  = getTags (ts :< t) e
>     getTags ts _            = (|)
>
>     process :: Bwd (REF :<: INTM) -> Bwd (EXTM -> INTM) -> Bwd INTM ->
>         INTM :=>: VAL -> Bwd VAL -> Simplifier Simplify
>     process qs gs hs (n :=>: nv) B0 = do
>         e' <- bquote B0 e
>         b' <- bquote B0 b
>         let b'' = b' ?? ARR (ENUMT e') PROP
>         return $ Simply qs gs $
>             L $ "xe" :. N (switchOp :@ [e', NV 0,
>                                         L $ "yb" :. PRF (N (b'' :$ A (NV 0))),
>                                         Prelude.foldr PAIR VOID (trail hs)])
>     process qs1 gs1 hs1 (n :=>: nv) (ts :< t) = forkNSupply "psEnumImp"
>         (forceSimplify gamma delta (b $$ A nv)) $
>         \ (btSimp, _) -> case btSimp of
>             SimplyAbsurd prf  -> return $ SimplyAbsurd (prf . (:$ A n))
>             Simply qs2 gs2 h2  -> do
>                 let gs2' = fmap (. (:$ A n)) gs2
>                 process (qs1 <+> qs2) (gs1 <+> gs2') (hs1 :< h2)
>                         (SU n :=>: SU nv) ts


To simplify |p = (x : s) => t| where |s| is not a proof set, we generate a fresh
reference and simplify |t| under the binder.

> propSimplify gamma delta p@(ALL s l) = do
>     s' <- bquote B0 s
>     freshRef (fortran l :<: s) $ \ refS -> 
>       forkNSupply  "psAll" 
>           (propSimplify gamma (delta :< (refS :<: s')) (l $$ A (NP refS))) 
>           (thingy s' refS)
>   where
>     thingy :: (NameSupplier m) => INTM -> REF -> Simplify -> m Simplify

If |t| is absurd, then |p| simplifies to |(x : s) => FF|. 

>     thingy s' refS (SimplyAbsurd prf) =
>       freshRef ("psA" :<: PRF (ALL s (LK ABSURD))) $ \ refA -> do
>         l' <- bquote B0 l
>         let l'' = l' :? ARR (PRF s') PROP
>         return $
>           SimplyOne  (refA :<: PRF (ALL s' (LK ABSURD)))
>                      (\ pv -> N (nEOp :@ [prf (pv :$ A (NP refS)),
>                                           PRF (ALL s' (LK ABSURD))]))
>                      (L $ "cabs2" :. N (nEOp :@ [N (P refA :$ A (NV 0)),
>                                                  PRF (N (l'' :$ A (NV 0)))]))

If |t| is trivial, then |p| is trivial.

>     thingy s' refS (SimplyTrivial prf) =
>         return $ SimplyTrivial (dischargeLots' (B0 :< refS) prf)

Otherwise, |p| simplifies to a conjunction of propositions |(x : s) =>
q| for each |q| in the simplification of |t|.


>     thingy s' refS (Simply qs gs h) = do
>         let pqs = fmap (dischargeRefAlls' (B0 :< (refS :<: s'))) qs
>         let pgs = fmap wrapper gs
>         let h2 = substitute qs (fmap (\ (q :<: ty) -> N (P q :$ A (NP refS))) pqs) h
>         let ph = dischargeLots' (B0 :< refS) h2
>         return (Simply pqs pgs ph)
>       where

The |wrapper| says how to get a proof |pg : p -> pq| given a proof |g : t -> q|.
Since |pq == (x : s) => q| we can give back a function that takes proofs
|pv : p| and |sv : s|, applies |pv| to |sv| to give a proof of |t|, then
applies |g| to this proof to get a proof of |q|.

>         wrapper :: (EXTM -> INTM) -> EXTM -> INTM
>         wrapper g pv = L $ "s" :. g (pv :$ A (NV 0))


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
>       m     <- optional $ simplifyBlue False gamma delta (sty :>: s) (tty :>: t)
>       sty'  <- bquote B0 sty
>       s'    <- bquote B0 s
>       tty'  <- bquote B0 tty
>       t'    <- bquote B0 t
>       let q = PRF (EQBLUE (sty' :>: s') (tty' :>: t'))
>       case m of
>           Just (SimplyTrivial prf) -> return $ SimplyTrivial
>               (N (prf :? q :$ Out))
>           Nothing ->
>              freshRef ("q" :<: PRF (EQBLUE (sty :>: s) (tty :>: t))) $ \ qRef ->
>                return $ SimplyOne  (qRef :<: q)
>                                    (CON . N)
>                                    (N (P qRef :$ Out))


If nothing matches, we can always try searching the context.

> propSimplify gamma delta p = propSearch gamma delta p


The |simplifyBlue| command attempts to simplify a blue equation using
refl, optionally unrolling it (calling eqGreen and simplifying the
resulting pieces), or just searching the context.

> simplifyBlue ::  Bool -> Bwd REF -> Bwd (REF :<: INTM) -> TY :>: VAL
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
>        sty'  <- bquote B0 sty
>        s'    <- bquote B0 s
>        return . SimplyTrivial $ N (P refl :$ A sty' :$ A s')
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
>    equality (SimplyAbsurd prf) = return $ SimplyAbsurd (prf . (:$ Out))
>    equality (Simply qs gs h) = return $ Simply  qs
>                                                 (fmap (. (:$ Out)) gs)
>                                                 (CON h)




The |propSearch| operation searches the context for a proof of the proposition,
and if it finds one, returns the trivial simplification. When |seekProof| finds
a proof in the context, it calls |backchain| to go under any implications and
test if the consequent matches the goal; if so, |backchain| then calls
|seekProof| to attempt to prove the hypotheses, in the context with the
backchained proposition removed. 

> propSearch :: Bwd REF -> Bwd (REF :<: INTM) -> VAL -> Simplifier Simplify
> propSearch gamma delta p = do
>     prf <- seekProof (gamma <+> fmap fstEx delta) F0 p
>     prf' <- bquote B0 prf
>     return $ SimplyTrivial prf'
>   where 
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

> forceSimplifyNamed :: Bwd REF -> Bwd (REF :<: INTM) -> VAL -> String ->
>     Simplifier (Simplify, Bool)
> forceSimplifyNamed gamma delta p hint  =
>     (propSimplify gamma delta p >>= return . (, True))
>     <|> simplifyNone hint (PRF p)
>   where
>       simplifyNone :: (NameSupplier m) => String -> TY -> m (Simplify, Bool)
>       simplifyNone hint ty = do
>           ty' <- bquote B0 ty
>           freshRef (nameHint hint ty :<: ty) $ \ ref ->
>               return (SimplyOne (ref :<: ty') N (NP ref), False)
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
>         Just (SimplyTrivial prf)  -> give prf >> return B0
>
>         Just (Simply qs _ h) -> do
>             qrs <- traverse makeSubgoal qs
>             give (substitute qs (fmap (N . termOf) qrs) h)
>             return qrs

The |makeSubgoal| command makes a new subgoal whose type corresponds to the type
of the given reference, and returns its term and value representations.

> makeSubgoal :: REF :<: INTM -> ProofState (EXTM :=>: VAL)
> makeSubgoal (ref :<: q') = do
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