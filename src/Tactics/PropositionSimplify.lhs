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
The judgment $\Gamma \Vdash P$ is not yet defined, but means $P$ can be proved
from hypotheses in $\Gamma$ by backchaining search.

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


We need a name supply for simplification, and use the |Maybe| monad to allow
failure. This could just as well be an arbitrary monad supporting these effects.

> type Simplifier x = ReaderT NameSupply Maybe x


We can transform a simplification of a proposition $P$ into a simplification of
another proposition $Q$ if we have functions from proofs of $Q$ to proofs of
$P$ (first argument) and from proofs of $P$ to proofs of $Q$ (second argument).

> simplifyTransform :: (EXTM -> EXTM) -> (INTM -> INTM) -> Simplify -> Simplify
> simplifyTransform e f (SimplyAbsurd prf)  = SimplyAbsurd (prf . e)
> simplifyTransform e f (Simply ps gs h)    = Simply ps (fmap (. e) gs) (f h)


\subsection{Simplification in Action}

The |propSimplify| command takes a global context, local context and proposition;
it attempts to simplify the proposition following the rules above.

> propSimplify :: Bwd REF -> Bwd (REF :<: INTM) -> VAL -> Simplifier Simplify


Simplifying $\Trivial$ and $\Absurd$ is remarkably easy.

> propSimplify _ _ ABSURD   = return (SimplyAbsurd   N)
> propSimplify _ _ TRIVIAL  = return (SimplyTrivial  VOID)


To simplify a conjunction $P \wedge Q$, we simplify each conjunct separately,
then call the |simplifyAnd| helper function to combine the results. If either
conjunct is absurd, then we can easily show that the conjunction is absurd.
Otherwise, we append the lists of conjuncts and pre-compose the proofs with
|Fst| or |Snd| as appropriate.

> propSimplify gamma delta (AND p q) = forkSimplify gamma delta p $
>     \ pr -> case fst pr of
>         SimplyAbsurd px    -> return $ SimplyAbsurd (px . (:$ Fst))
>         Simply pis pgs ph  -> forkSimplify gamma delta q $
>             \ qr -> case fst qr of
>                 SimplyAbsurd qx    -> return $ SimplyAbsurd (qx . (:$ Snd))
>                 Simply qis qgs qh  -> return $ Simply (pis <+> qis)
>                     (fmap (. (:$ Fst)) pgs <+> (fmap (. (:$ Snd)) qgs))
>                     (PAIR ph qh)


To simplify $\ALL{x}{\prf{P}} L x$, we first try to simplify $P$:

> propSimplify gamma delta (ALL (PRF p) l) =
>    forkSimplify' (fortran l) gamma delta p antecedent
>   where
>     antecedent :: (Simplify, Bool) -> Simplifier Simplify

If $P$ is absurd then the implication is trivial, which we can prove by absurdity
elimination whenever someone gives us a proof of $P$:

>     antecedent (SimplyAbsurd px, _) = do
>       l'   <- bquote B0 l
>       l''  <- annotate l' (ARR (PRF p) PROP)
>       return . SimplyTrivial . L $ "absurd" :.
>           (N (nEOp :@ [px (V 0), PRF (N (l'' :$ A (NV 0)))]))

If $P$ is trivial, then we go under $L$ by applying the proof and simplify the
resulting proposition $Q$. The implication simplifies to the result of
simplifying $Q$, with the proofs constructed by $\lambda$-abstracting
in one direction and applying the proof of $P$ in the other direction.

>     antecedent (SimplyTrivial pt, _) =
>         forkSimplify gamma delta (l $$ A (evTm pt))
>             (return . simplifyTransform (:$ A pt) LK . fst)

If $P$ simplifies nontrivially, we have a bit more work to do. We add the
simplified conjuncts of $P$ to the context and apply $L$ to the proof of
$P$ in the extended context, giving a new proposition $Q$. We then simplify $Q$.

>     antecedent x@(Simply pis pgs ph, simplifiedP) = do
>         let q = l $$ A (evTm ph)
>         forkSimplify gamma (delta <+> pis) q (consequent x)
     
>     consequent :: (Simplify, Bool) -> (Simplify, Bool) -> Simplifier Simplify

If $Q$ is absurd, then the simplified proposition is an implication from the
simplified conjuncts of $P$ to $\Absurd$. The proof of the original implication
is by absurdity elimination, applying the |pgs| to the proof of $P$ to get proofs
of the |pis|, then applying the simplified proposition to these.

>     consequent (Simply pis pgs ph, _) (SimplyAbsurd qx, _) = do
>             let pisImplyFF = dischargeAll pis (PRF ABSURD)
>             freshRef ("ri" :<: evTm pisImplyFF) $ \ riRef -> do
>                 l'   <- bquote B0 l
>                 l''  <- annotate l' (ARR (PRF p) PROP)
>                 rh   <- mkFun $ \ pref ->
>                             let  piPrfs = fmap ($ (P pref)) pgs
>                             in   N (nEOp :@ [
>                                      N (P riRef $## piPrfs),
>                                      PRF (N (l'' :$ A (NP pref)))
>                                  ])
>                 return $ SimplyOne (riRef :<: pisImplyFF)
>                     (\ rt -> dischargeLam (fmap fstEx pis) (qx (rt :$ A ph)))
>                     rh


If the consequent $Q$ is trivial, then the implication is trivial, which we can
prove by applying the |pgs| to a hypothetical proof of $P$ to get proofs of the
|pis|, then substituting these for the |pis| in the proof of $Q$.

>     consequent (Simply pis pgs ph, _) (SimplyTrivial qt, _) = do
>             rh <- mkFun $ \ pref -> substitute pis (fmap ($ (P pref)) pgs) qt
>             return $ SimplyTrivial rh

Otherwise, if $Q$ simplifies, then the implication simplifies to a conjunction of
implications. Each implication is from the simplified components of $P$ to a
single simplified component of $Q$. To prove the original implication, we
assume a proof of $P$, then construct proofs of the |pis| from it and proofs of
the |qis| by applying the proofs of the |ris| to these. We can then substitute
these proofs for the |pis| and |qis| in the proof of $Q$.

>     consequent (Simply pis pgs ph, simpP) (Simply qis qgs qh, simpQ) 
>         | simpP || simpQ = do
>             let ris = fmap (dischargeAllREF pis) qis
>             let rgs = fmap wrapper qgs
>             rh <- mkFun $ \ pref ->
>                 let piPrfs  = fmap ($ (P pref)) pgs
>                     qiPrfs  = fmap (\ (ri :<: _) -> N (P ri $## piPrfs)) ris
>                 in substitute pis piPrfs (substitute qis qiPrfs qh)
>             return $ Simply ris rgs rh
>           where
>             wrapper :: (EXTM -> INTM) -> EXTM -> INTM
>             wrapper qg pv = dischargeLam (fmap fstEx pis) (qg (pv :$ A ph))


If we get to this point, neither the antecedent nor the consequent simplified,
so we had better give up.

>     consequent (_, False) (_, False) = (|) 


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
>     process qs1 gs1 hs1 (n :=>: nv) (ts :< t) =
>         forkSimplify gamma delta (b $$ A nv) $ \ (btSimp, _) -> case btSimp of
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
>         return $ SimplyTrivial (dischargeLam (B0 :< refS) prf)

Otherwise, |p| simplifies to a conjunction of propositions |(x : s) =>
q| for each |q| in the simplification of |t|.


>     thingy s' refS (Simply qs gs h) = do
>         let pqs = fmap (dischargeAllREF (B0 :< (refS :<: s'))) qs
>         let pgs = fmap wrapper gs
>         let h2 = substitute qs (fmap (\ (q :<: ty) -> N (P q :$ A (NP refS))) pqs) h
>         let ph = dischargeLam (B0 :< refS) h2
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
>        Right q        -> forkSimplify gamma delta q
>            (return . simplifyTransform (:$ Out) CON . fst)


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
>         ssPrfs <- traverse (seekProof (rs <>< fs) F0 . unPRF . pty) ss
>         return $ pval ref $$$ fmap A ssPrfs
>
>     unPRF :: VAL -> VAL
>     unPRF (PRF p) = p


The |forceSimplify| function is a variant of |propSimplify| that guarantees to
give a result, by trying to simplify the proposition and yielding an identical
copy if simplification fails. It also returns a boolean indicating whether
simplification occurred. This is useful in cases such as |&&|, where we know
we can do some simplification even if the conjuncts do not simplify.
The first argument is an optional hint for the name of the reference.

> forceSimplify :: String -> Bwd REF -> Bwd (REF :<: INTM) -> VAL ->
>     Simplifier (Simplify, Bool)
> forceSimplify hint gamma delta p =
>     (propSimplify gamma delta p >>= return . (, True))
>     <|> simplifyNone (PRF p)
>   where
>       simplifyNone :: (NameSupplier m) => TY -> m (Simplify, Bool)
>       simplifyNone ty = do
>           ty' <- bquote B0 ty
>           freshRef (nameHint ty :<: ty) $ \ ref ->
>               return (SimplyOne (ref :<: ty') N (NP ref), False)
>   
>       nameHint :: VAL -> String
>       nameHint _ | not (null hint)  = hint
>       nameHint (NP (n := _))        = fst (last n)
>       nameHint (L (HF s _))         = s
>       nameHint (L (H _ s _))        = s
>       nameHint (L (s :. _))         = s
>       nameHint _                    = "xnh"

To ensure correctness of fresh name generation, we need to fork the name supply
before performing additional simplification, so we define helper functions to
fork then call |forceSimplify|.

> forkSimplify :: Bwd REF -> Bwd (REF :<: INTM) -> VAL ->
>     ((Simplify, Bool) -> Simplifier a) -> Simplifier a
> forkSimplify = forkSimplify' ""

> forkSimplify' :: String -> Bwd REF -> Bwd (REF :<: INTM) -> VAL ->
>     ((Simplify, Bool) -> Simplifier a) -> Simplifier a
> forkSimplify' hint gamma delta p f = forkNSupply "fS"
>     (forceSimplify hint gamma delta p) f

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
>         Just (SimplyTrivial prf)  -> give prf >> return B0
>         Just (Simply qs _ h)      -> do
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