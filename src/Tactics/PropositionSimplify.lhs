\section{Propositional Simplification}
\label{sec:Tactics.PropositionSimplify}

\newcommand{\simpto}{\leadsto}
\newcommand{\and}{\wedge}
\newcommand{\conj}[2]{\bigwedge_{#2} {#1}_{#2}}
\newcommand{\BlueEq}[4]{(\Bhab{#2}{#1}) \EQ (\Bhab{#4}{#3})}
\newcommand{\GreenEq}[4]{(\Bhab{#2}{#1}) \green{\leftrightarrow} (\Bhab{#4}{#3})}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, FlexibleInstances,
>              PatternGuards, TupleSections, ExplicitForAll #-}

> module Tactics.PropositionSimplify where

> import Prelude hiding (any, foldl, exp)

> import ShePrelude

> import Control.Applicative 
> import Control.Monad.Reader

> import Data.List
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.NatFinVec
> import Kit.MissingLibrary
> import Kit.Trace

> import Evidences.Tm
> import Evidences.NameSupply
> import Evidences.DefinitionalEquality
> import Evidences.ErrorHandling
> import Evidences.TypeCheckRules
> import Evidences.Primitives

> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import ProofState.Interface.Name
> import ProofState.Interface.Definition
> import ProofState.Interface.Solving

%endif

\subsection{Setting the Scene}

A proposition is \emph{nice}\index{nice proposition} if it is:
\begin{itemize}
\item a neutral term of type $\Prop$;
\item an equation with (at least) one neutral side;
\item $P \Imply Q$, with $P$ nice and $Q$ nice or $\Absurd$; or
\item $\ALL{x}{S} P$, with $S$ not a proof and $P$ nice or $\Absurd$.
\end{itemize}
A proposition is \emph{simple}\index{simple proposition} if it is
$\Absurd$ or a conjunction of zero or more nice propositions (where
$\Trivial$ is the empty conjunction).

We write $\Gamma \Tn P \simpto R$ to mean that the proposition $P$ in
context $\Gamma$ simplifies to the simple proposition $R$. The rules
in Figure~\ref{fig:Tactics.PropositionSimplify.rules} define this
judgment, and the implementation follows these rules.  The judgment
$\Gamma \Vdash P$ is not yet defined, but means $P$ can be proved from
hypotheses in $\Gamma$ by backchaining search. There's also a rule
missing about equality proofs being simplified by unrolling.

\begin{figure}[ht]

$$
\CAxiom{\Gamma \Tn \Trivial \simpto \Trivial}
\qquad
\Rule{\Gamma \nVdash \Absurd}
     {\Gamma \Tn \Absurd \simpto \Absurd}
$$

$$
\Rule{\Gamma \Tn P \simpto \Absurd}
     {\Gamma \Tn P \and Q \simpto \Absurd}
\qquad
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad
      \Gamma, \vec{P_i} \Tn Q \simpto \Absurd}
     {\Gamma \Tn P \and Q \simpto \Absurd}
\qquad
\Rule{\Gamma \Tn P \simpto \conj{P}{i}  \quad
      \Gamma, \vec{P_i} \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn P \and Q \simpto \conj{P}{i} \and \conj{Q}{j}}
$$

$$
\Rule{\Gamma \Tn P \simpto \Absurd}
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
\Rule{\Gamma, \Bhab{x}{S} \Tn Q \simpto \conj{Q}{j}}
     {\Gamma \Tn \ALL{x}{S} Q \simpto \bigwedge_j (\ALL{x}{S} Q_j)}
$$

$$
\CAxiom{\Gamma \Tn \BlueEq{S}{s}{S}{s} \simpto \Trivial}
\qquad
\Rule{\Gamma \Vdash P}
     {\Gamma \Tn P \simpto \Trivial}
$$

\caption{Propositional simplification rules}
\label{fig:Tactics.PropositionSimplify.rules}
\end{figure}


Given $\Gamma \Tn \Bhab{P}{\Prop}$ and a starting level $l$ above all
levels in $\Gamma$, the propositional simplifier will either:
\begin{itemize}
\item discover that $P$ is absurd and return |SimplyAbsurd prfPtoFF|,
  where $\Gamma \Tn \Bhab{\mathit{prfPtoFF}}{\prf{(P \Imply \Absurd)}}$;
\item simplify $P$ to a conjunction $\conj{P}{i}$ and return
  |Simply simpP prfP|; or
\item fail and return |CannotSimplify|.
\end{itemize}

In the second case, each element of the list |simpP| is a pair
$(P_i, \mathit{prfPtoPi})$ where 
$\Gamma, \vec{P_j} \Tn \Bhab{P_i}{\Prop}$ and
$\Gamma, \vec{P_j} \Tn \Bhab{\mathit{prfPtoPi}}{\prf{(P \Imply P_i)}}$
for $j = 0, \ldots, i-1$. Moreover
$\Gamma, \vec{P_i} \Tn \Bhab{\mathit{prfP}}{\prf{P}}$. Note that the
proof of $P_j$ in the context has de Bruijn level $l+j$ when it appears in
|prfPtoPi| or |prfP|.


> data Simplify where
>     SimplyAbsurd    :: EXP -> Simplify
>     Simply          :: Bwd (EXP, EXP) -> EXP -> Simplify
>     CannotSimplify  :: Simplify


A couple of useful special cases: the trivial simplification (empty
conjunction) and simplification to a single alternative proposition:

> pattern SimplyTrivial prfP          = Simply B0 prfP
> pattern SimplyOne p0 prfPtoP0 prfP  = Simply (B0 :< (p0, prfPtoP0)) prfP


We can transform a simplification of a proposition $Q$ into a
simplification of another proposition $P$ given proofs of $P \Imply Q$
and $Q \Imply P$.

> mapSimp ::  Int -> EXP -> EXP -> EXP -> Simplify -> Simplify
> mapSimp lev q prfPtoQ prfQtoP CannotSimplify         =
>     SimplyOne q prfPtoQ (prfQtoP $$. (P (lev, "PS-MS", PRF q) :$ B0))
> mapSimp lev q prfPtoQ prfQtoP (SimplyAbsurd prfQtoFF)  =
>     SimplyAbsurd (prfQtoFF .* prfPtoQ)
> mapSimp lev q prfPtoQ prfQtoP (Simply simpQ prfQ)         = Simply
>     (fmap (\ (qi, prfQtoQi) -> (qi, prfQtoQi .* prfPtoQ)) simpQ)
>     (prfQtoP $$. prfQ)


The |ensureSimple| function converts simplification failures into
simplifications to the same proposition, given the next fresh level
and the proposition that was originally simplified. This should only
be used when some other simplification is definitely taking place.

> ensureSimple :: Int -> EXP -> Simplify -> (Simplify, Bool)
> ensureSimple lev p CannotSimplify  =
>     (SimplyOne p idF (P (lev, "PS-ES", PRF p) :$ B0), False)
> ensureSimple lev p pSimp           = (pSimp, True)


Sometimes it is useful to view an absurd result as a simplification to
the single proposition $\Absurd$. The |absurdlySimple| function
converts to this representation and |simplyAbsurd| returns to the
usual representation.

> absurdlySimple :: Int -> EXP -> Simplify -> Simplify
> absurdlySimple lev p (SimplyAbsurd prfPtoFF) =
>     SimplyOne ZERO prfPtoFF $
>         wr (def falseElimDEF) (P (lev, "PS-ABSS", PRF ZERO) :$ B0) (PRF p)
> absurdlySimple lev p pSimp = pSimp

> simplyAbsurd :: Simplify -> Simplify
> simplyAbsurd (SimplyOne p prfPtoFF _) | ZERO <- ev p = SimplyAbsurd prfPtoFF
> simplyAbsurd pSimp = pSimp


Here is a common pattern for constructing level environments to
substitute out level variables occurring in proofs. The backwards list
should contain proofs of each simplified proposition, where each proof
may depend on proofs of earlier propositions; a level environment will
be constructed that closes each proof under the preceding proofs. 

> mkLEnv :: Int -> Bwd (Tm {Body, Exp, n}) -> LEnv {n}
> mkLEnv l es = mkLEnv' (const id) l (trail es)

Actually, sometimes we need slightly more precision. This function
allows a proof for each proposition to be constructed its level
(useful when reindexing) and an element of the (now forwards)
list. You are not expected to understand this.

> mkLEnv' :: (Int -> a -> Tm {Body, Exp, n}) -> Int -> [a] -> LEnv {n}
> mkLEnv' f l []      = []
> mkLEnv' f l (e:es)  = let r = mkLEnv' f (l+1) es
>                       in (l, (r, INil) :/ f l e) : r


Here are some useful combinators for building proof terms.

> (.*) :: EXP -> EXP -> EXP -- composition
> g .* f = la "x" $ \ x -> wk g :$ (B0 :< A (wk f :$ (B0 :< A x)))
>
> hdF :: EXP -- project out the head
> hdF = L ENil "x" (V Fz :$ (B0 :< Hd))
>
> tlF :: EXP -- project out the tail
> tlF = L ENil "x" (V Fz :$ (B0 :< Tl))
>
> kF :: EXP -- the k combinator
> kF = L ENil "x" (LK (V Fz :$ B0))
>
> idF :: EXP -- the identity function
> idF = L ENil "x" (V Fz :$ B0)


And some other random rubbish:

> fmapSnd f = fmap (\ (x, y) -> (x, f y))

> isFF :: VAL -> Bool
> isFF ZERO  = True
> isFF _     = False

> typesOf :: Bwd (EXP, EXP) -> Bwd TY
> typesOf = fmap (PRF . fst)


\subsection{Simplification in Action}

The |propSimplify| command takes a context and proposition; it
attempts to simplify the proposition following the rules above. If the
result is |Simply| one or more new propositions then these will be
simpler than the original proposition. It will return |CannotSimplify|
if no simplification is possible, rather than |Simply| the original
proposition. If the result is |SimplyAbsurd| then no simplification is
guaranteed to have taken place (i.e. the proposition might have been
syntactically $\Absurd$ already).

The first argument is the next fresh level, as usual, and the second
is the telescope of parameters in the context. If the result is of the
form |Simply simpP prfP|, then |prfP| treats the first components of
|simpP| as an extension to the context (i.e. parameters with levels
starting at the next fresh level).

Simplifying $\Trivial$ is remarkably easy. We could do something
similar for $\Absurd$, but in fact we don't, as we want invoke the
proof search machinery, which corresponds to looking for an
inconsistentcy in the context. For conjunctions, implications, foralls
and equations we invoke the relevant helper function. If nothing else
matches, we can always try searching the context.

> propSimplify :: NameSupplier m => Int -> Bwd TY -> VAL -> m Simplify
> propSimplify lev delta ONE        = return $ SimplyTrivial  ZERO
> propSimplify lev delta (AND p q)  = simplifyConj lev delta p q
> propSimplify lev delta (ALL s r)  = case ev s of
>     PRF p  -> simplifyImp lev delta p r
>     _      -> simplifyAll lev delta s r
> propSimplify lev delta (EQ sty s tty t) = 
>     simplifyEq lev delta (sty :>: s) (tty :>: t)
> propSimplify lev delta p = return $ propSearch lev delta p


\subsubsection{Conjunctions}

To simplify a conjunction $P \wedge Q$, we first try to simplify
$P$. If it is absurd then the conjunction is absurd. Otherwise, we add
the simplified $P_i$ to the context and simplify $Q$, then combine the
results. The context extension when simplifying $Q$ means that the
levels are correct when we combine the results.

> simplifyConj ::  NameSupplier m =>
>                     Int -> Bwd TY -> EXP -> EXP -> m Simplify
> simplifyConj lev delta p q = forkSimplify lev delta (ev p) $
>   \ pSimp -> case fst $ ensureSimple lev p pSimp of
>     SimplyAbsurd prfPtoFF  -> return $ SimplyAbsurd (prfPtoFF .* hdF)
>     Simply simpP prfP      ->
>         let lev'    = lev + bwdLength simpP
>             delta'  = delta <+> typesOf simpP
>         in forkSimplify lev' delta' (ev q) $
>           \ qSimp -> case fst $ ensureSimple lev' q qSimp of
>             SimplyAbsurd prfQtoFF -> return $ SimplyAbsurd $
>                   L ENil "prfPandQ" $
>                     ((mkLEnv lev (fmap foo simpP), INix) :/ prfQtoFF) :$
>                       (B0 :< A (V Fz :$ (B0 :< Tl)))
>                   where
>                     foo (_, prfPtoPi) = wk prfPtoPi :$ (B0 :< A (V Fz :$ (B0 :< Hd)))

>             Simply simpQ prfQ -> return $ Simply
>                 (fmapSnd (.* hdF) simpP <+> (fmapSnd (.* tlF) simpQ))
>                 (PAIR prfP prfQ)


\subsubsection{Implications}

To simplify $P \Imply R$, we first try to simplify $P$:

> simplifyImp ::  NameSupplier m =>
>                    Int -> Bwd TY -> EXP -> EXP -> m Simplify
> simplifyImp lev delta p r =
>   forkSimplify lev delta (ev p) $
>   \ pSimp -> case ensureSimple lev p pSimp of


If $P$ is absurd then the implication is trivial, which we can prove
by absurdity elimination whenever someone gives us a proof of $P$:

>     (SimplyAbsurd prfPtoFF, _) ->
>       return $ SimplyTrivial $
>         la "psPrfP" $ \ prfP ->
>           wr (def falseElimDEF) (wr prfPtoFF prfP) (PRF (wr r prfP))


If $P$ is not absurd, we have lots more work to do. We add (the
simplified conjuncts of) $P$ to the context and apply $R$ to the proof
of $P$ in the extended context, giving a new proposition $Q$. We then
simplify $Q$.

>     (Simply simpP prfP, pWasSimplified) -> do
>      let  q       = r $$. prfP
>           qv      = ev q
>           numPis  = bwdLength simpP
>           lev'    = lev + numPis
>           delta'  = delta <+> typesOf simpP
>      forkSimplify lev' delta' qv $ \ qSimp ->
>       case qSimp of

If $Q$ is syntactically $\Absurd$, could not be proved from an
inconsistency in the context, and $P$ could not be simplified, then we
cannot simplify it further.

>        SimplyAbsurd _ | isFF qv && not pWasSimplified -> return CannotSimplify

If both $P$ and $Q$ cannot be simplified, then neither can the implication.

>        CannotSimplify | not pWasSimplified  -> return CannotSimplify


Otherwise, the implication simplifies to a conjunction of implications
from the telescope of simplified components of $P$ to a single
simplified component of $Q$. To prove the original implication, we
assume a proof of $P$, then construct proofs of the |pis| from it and
proofs of the |qis| by applying the proofs of the |ris| to these. We
can then substitute these proofs for the |pis| and |qis| in the proof
of $Q$.

Note that this case covers |SimplyAbsurd| as well (using
|absurdlySimple| and |simplyAbsurd| to translate between
representations).

>        _ -> return $ simplyAbsurd $ bwdVec simpP bungle
>          where
>           Simply simpQ prfQ = fst $ ensureSimple lev' q $ absurdlySimple lev' q qSimp

>           bungle :: pi (n :: Nat). BVec {n} (EXP, EXP) -> Simplify
>           bungle n simpP' = Simply (fmap liftPis simpQ) prfPtoR
>            where
>             (stuff, lk) = bvecLev' simpP'                   

>             liftPis :: (EXP, EXP) -> (EXP, EXP)
>             liftPis (qi, prfQtoQi) = (piLift n stuff qi, pToQ_to_PisToQi prfQtoQi)
>
>             bvecLev' :: BVec {n} (EXP, EXP) -> (BVec {n} (Int, String, TY), Int)
>             bvecLev' BV0 = (BV0, lev)
>             bvecLev' (pgs :<<<: (pi, _)) = (xs :<<<: (l, "psWoo", PRF pi), l+1)
>               where (xs, l) = bvecLev' pgs
>                                
>             pToQ_to_PisToQi :: EXP -> EXP
>             pToQ_to_PisToQi prfQtoQi = la "psPtoQ" $ \ pToQ ->
>                 ([(lk, pToQ)], INix) :/
>                 (lamLift n stuff $
>                     wr prfQtoQi (P (lk, "PS-WARK", p ==> q) :$ (B0 :< A (wk prfP))))
>
>             prfPtoR :: EXP
>             prfPtoR = la "psPrfP" $ \ prfP -> (pibits ++ qibits, INix) :/ prfQ
>                          
>             pibits = mkLEnv lev $ fmap (\ (_, prfPtoPi) -> wr prfPtoPi (V Fz :$ B0)) simpP
>
>             qibits = mkLEnv' (\ lev _ -> P (lev - numPis, "PS-QGSFROMP", error "wark")
>                                  :$ pisPrfs simpP) lev' (trail simpQ)
>
>             pisPrfs :: Bwd (EXP, EXP) -> Bwd (Elim (Tm {Body, Exp, S Z}))
>             pisPrfs B0                 = B0
>             pisPrfs (pgs :< (_, prfPtoPi))  = pisPrfs pgs :< A
>                 (((pibits, INix) :/ prfPtoPi) :$ (B0 :< A (V Fz :$ B0)))



\subsubsection{Universal quantification}

To simplify $\ALL{x}{S} R x$ where $S$ is not of the form $\prf{P}$,
we introduce a fresh parameter and apply $R$ to it to get the
proposition $Q$ under the binder, which we can then simplify.

> simplifyAll ::  NameSupplier m =>
>                     Int -> Bwd TY -> EXP -> EXP -> m Simplify
> simplifyAll lev delta s r =
>   let q   = r $$. (P (lev, "PS-ALL-X-S", s) :$ B0)
>       qv  = ev q
>   in forkSimplify (lev+1) (delta :< s) qv $
>     \ qSimp -> return $ case qSimp of


If $Q$ does not simplify, then we're sunk.

>       CannotSimplify -> CannotSimplify


If $Q$ is syntactically $\Absurd$ and we haven't found an
inconsistency in the context, then we're also sunk.

>       SimplyAbsurd _ | isFF qv -> CannotSimplify  


Otherwise, $Q$ simplifies to a conjunction of propositions $Q_i$, and
$\ALL{x}{S} R x$ simplifies to a conjunction of propositions
$\ALL{x}{S} Q_i$.


>       _ -> simplyAbsurd $ Simply simpAllSR prfAllSR
>         where
>             Simply simpQ prfQ = absurdlySimple (lev+1) q qSimp
>
>             -- Replace $Q_i$ with $\ALL{x}{S} Q_i$
>             simpAllSR = fmap absS simpQ
>
>             absS :: (EXP, EXP) -> (EXP, EXP)
>             absS (qi, prfQtoQi) =
>                 (  ("psx", s) ->> \ x -> ([(lev, x)], INix) :/ qi
>                 ,  la "psPrfAllSR" $ \ prfAllSR ->
>                        la "psx" $ \ x -> (([(lev, x)], INix) :/ prfQtoQi) :$
>                                              (B0 :< A (prfAllSR x))
>                 )
>
>             -- Proof of $\ALL{x}{S} R x$ with $\ALL{x}{S} Q_i$s in context
>             prfAllSR = (la "psx" $ \ x ->
>                 ((lev, x) : mkLEnv' bungle (lev+1) (trail simpAllSR), INix) :/ prfQ)
>
>             bungle lev (allSQi, _) = P (lev-1, "PS-FOO", PRF allSQi)
>                                          :$ (B0 :< A (V Fz :$ B0))







To simplify a proposition that is universally quantified over a (completely
canonical) enumeration, we can simplify it for each possible value.

< propSimplify delta p@(ALL (ENUMT e) b) | Just ts <- getTags B0 e = 
<     process B0 B0 B0 (ZE :=>: ZE) ts
<   where
<     getTags :: Bwd VAL -> VAL -> Maybe (Bwd VAL)
<     getTags ts NILE         = (| ts |)
<     getTags ts (CONSE t e)  = getTags (ts :< t) e
<     getTags ts _            = (|)
<
<     process :: Bwd (REF :<: INTM) -> Bwd (EXTM -> INTM) -> Bwd INTM ->
<         INTM :=>: VAL -> Bwd VAL -> Simplifier Simplify
<     process qs gs hs (n :=>: nv) B0 = do
<         e' <- bquote B0 e
<         b' <- bquote B0 b
<         let b'' = b' ?? ARR (ENUMT e') PROP
<         return $ Simply qs gs $
<             L $ "xe" :. N (switchOp :@ [e', NV 0,
<                                         L $ "yb" :. PRF (N (b'' :$ A (NV 0))),
<                                         Prelude.foldr PAIR VOID (trail hs)])
<     process qs1 gs1 hs1 (n :=>: nv) (ts :< t) =
<         forkSimplify delta (b $$ A nv) $ \ (btSimp, _) -> case btSimp of
<             SimplyAbsurd prf  -> return $ SimplyAbsurd (prf . (:$ A n))
<             Simply qs2 gs2 h2  -> do
<                 let gs2' = fmap (. (:$ A n)) gs2
<                 process (qs1 <+> qs2) (gs1 <+> gs2') (hs1 :< h2)
<                         (SU n :=>: SU nv) ts





\subsubsection{Equations}

The |simplifyEq| command attempts to simplify an equation using
|refl|, decomposing it using |eqUnfold|, or just searching the
context.

> simplifyEq ::  NameSupplier m => 
>                      Int -> Bwd TY -> TY :>: EXP -> TY :>: EXP ->
>                          m Simplify 
> simplifyEq lev delta (sty :>: s) (tty :>: t) 
>     |  equal lev (SET :>: (sty, tty))
>     ,  equal lev (sty :>: (s, t)) =
>   return $ SimplyTrivial (Refl sty s :$ B0)

> simplifyEq lev delta (sty :>: s) (tty :>: t) 
>     |  (cs :- cas)   <- ev sty
>     ,  (ct :- cat)   <- ev tty 
>     ,  Just (k, es)  <- eqUnfold ((cs, cas) :>: s) ((ct, cat) :>: t) = 
>   case (k, es) of
>     (_,     [])      -> return $ SimplyTrivial (k :- [])
>     (Con,   [p])     -> mapSimp lev p (L ENil "x" (V Fz :$ (B0 :< Out)))
>                                       (L ENil "x" (Con :- [V Fz :$ B0]))
>                             <$> propSimplify lev delta (ev p)
>     (Pair,  [p, q])  -> mapSimp lev (AND p q) pairEta pairEta
>                             <$> propSimplify lev delta (AND p q)
>     _                -> return $ propSearch lev delta (EQ sty s tty t)

>   where pairEta = L ENil "x" $ PAIR (V Fz :$ (B0 :< Hd)) (V Fz :$ (B0 :< Tl))

> simplifyEq lev delta (sty :>: s) (tty :>: t) =
>     return $ propSearch lev delta (EQ sty s tty t)



\subsubsection{Proof search}

The |propSearch| operation searches the context for a proof of the
proposition, and if it finds one, returns the trivial
simplification. When |seekProof| finds a proof in the context, it
calls |backchain| to go under any implications and test if the
consequent matches the goal; if so, |backchain| then calls |seekProof|
to attempt to prove the hypotheses, in the context with the
backchained proposition removed.

> propSearch :: Int -> Bwd TY -> VAL -> Simplify
> propSearch lev delta p =
>     case (seekProof lev (ascending (lev-1) delta) F0 p, p) of
>         (Just prfP,  _)     -> SimplyTrivial prfP
>         (Nothing,    ZERO)  -> SimplyAbsurd idF
>         (Nothing,    _)     -> CannotSimplify
>   where 
>     ascending (-1)  B0         = B0
>     ascending lev   (bs :< b)  = ascending (lev-1) bs :< (lev, b)
>
>     seekProof :: Int -> Bwd (Int, TY) -> Fwd (Int, TY) -> VAL -> Maybe EXP
>     seekProof lev B0 _ _              = (|)
>     seekProof lev (rs :< (l, r)) fs p = case ev r of
>         PRF q  ->   backchain lev rs (l, q) fs B0 p (ev q)
>                <|>  seekProof lev rs ((l, r) :> fs) p
>         _      ->   seekProof lev rs ((l, r) :> fs) p
>  
>     backchain :: Int -> Bwd (Int, TY) -> (Int, EXP) -> Fwd (Int, TY) -> Bwd TY -> VAL -> VAL -> Maybe EXP
>     backchain lev rs lr fs ss p (ALL h t) | PRF s <- ev h =
>         backchain (lev+1) rs lr fs (ss :< s) p
>             -- This doesn't look right but I can't seem to break it
>             (ev (t $$. (P (lev, "ook", PRF s) :$ B0))) 
>                                                                       
>     backchain lev rs (l, r) fs ss p q = do
>         guard $ equal lev $ PROP :>: (exp p, exp q)
>         ssPrfs <- traverse (seekProof lev (rs <>< fs) F0 . ev) ss
>         return $ P (l, "PS-BC", PRF r) :$ fmap A ssPrfs
>


\subsection{Invoking Simplification}

When in the |ProofState|, we can simplify a proposition using the
current level and context:

> runPropSimplify :: VAL -> ProofState Simplify
> runPropSimplify p = do
>     lev  <- getDevLev
>     es   <- getParamsInScope
>     ns   <- askNSupply
>     runReaderT (propSimplify lev (bwdList es) p) ns


To ensure correctness of fresh name generation, we need to fork the
name supply before performing additional simplification, so we define
helper functions to fork then call |propSimplify| or |forceSimplify|.

> forkSimplify :: NameSupplier m => Int -> Bwd TY -> VAL ->
>                     (Simplify -> m a) -> m a
> forkSimplify l delta p = forkNSupply "fS" (propSimplify l delta p)



The |propSimplifyHere| command attempts propositional simplification
on the current location, which must be an open goal of type |PRF p|
for some |p|.  If it is unable to simplify |p| or simplifies it to
|FF|, it will fail and throw an error. Otherwise, it will create zero
or more new subgoals (from the conjuncts of the simplified
proposition, if any), solve the current goal with the subgoals, and
return a list of their types.

> propSimplifyHere :: ProofState (Bwd EXP)
> propSimplifyHere = do
>     simpTrace "propSimplifyHere"
>     PRF p  <- ev <$> getHoleGoal
>     pSimp  <- runPropSimplify (ev p)
>     case pSimp of
>         CannotSimplify -> 
>             throwError' $ err "propSimplifyHere: unable to simplify."
>         SimplyAbsurd prfPtoFF -> do
>             simpTrace $ "Absurd with proof\n" ++ show prfPtoFF
>             throwError' $ err "propSimplifyHere: oh no, goal is absurd!"
>         SimplyTrivial prfP  -> do
>             simpTrace $ "Solved with proof\n" ++ show prfP
>             give prfP
>             return B0
>         Simply simpP prfP    -> do
>             simpTrace $ "Simplified to\n" ++
>                 intercalate "\n" (trail (fmap show simpP)) ++
>                 "\nwith proof\n" ++ show prfP
>             prfPis <- traverse (make . ("q" :<:) . PRF . fst) simpP
>             lev <- getDevLev
>             give $ (mkLEnv lev prfPis, INix) :/ prfP
>             return $ fmap fst simpP

The |propSimplify| tactic attempts to simplify the type of the current
goal, which should be propositional. Usually one will want to use
|simplify| instead, or simplification will happen automatically (with
the |let| and |<=| tactics), but this is left for backwards
compatibility.

> import -> CochonTacticsCode where
>     propSimplifyTactic :: ProofState String
>     propSimplifyTactic = do
>         subs <- propSimplifyHere 
>         case subs of
>             B0  -> return "Solved."
>             _   -> do
>                 subStrs <- traverse prettyProp subs
>                 nextGoal
>                 return ("Simplified to:\n" ++ 
>                     foldMap (\s -> s ++ "\n") subStrs)
>       where
>         prettyProp :: EXP -> ProofState String
>         prettyProp ty = renderHouseStyle <$> prettyPS (PROP :>: ty)

> import -> CochonTactics where
>   nullaryCT "propsimplify" propSimplifyTactic
>       "propsimplify - applies propositional simplification to the current goal." :