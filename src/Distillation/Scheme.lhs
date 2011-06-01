\section{The Scheme distiller}
\label{sec:Distillation.Scheme}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Scheme where

> import Control.Applicative

> import Text.PrettyPrint.HughesPJ (Doc)

> import Kit.BwdFwd

> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

> import Distillation.Distiller

> import DisplayLang.DisplayTm
> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import Evidences.Tm
> import Evidences.NameSupply

> import Kit.NatFinVec

%endif


\subsection{Distilling schemes}

Distilling a scheme is similar in spirit to distilling a $\Pi$-type,
in particular the $\lambda$-abstraction of its codomain
(section~\ref{subsec:Distillation.Distiller.intm}). Provided a |Scheme
INTM|, we compute the same scheme structure, with Display terms
instead.

To do so, we proceed structurally, using |distill| on types and,
recursively, |distillScheme| on schemes. Each time we go through a
$\Pi$, we go under a binder; therefore we need to be careful to turn
de Bruijn indices into the freshly introduced references.

This distiller takes the list of local entries we are working under,
as well as the collected list of references we have made so far. It
turns the |INTM| scheme into an a Display term scheme with relative
names.

> distillScheme ::  (Int, Bwd (Int, String, TY)) -> Scheme -> 
>                       ProofState (DScheme, TY)

On a ground type, there is not much to be done: |distill| does the
distillation job for us.

> distillScheme lps (SchType ty) = do
>     dty <- distill (SET :>: ev ty) lps
>     return (SchType dty, ty)

On an explicit $\Pi$, the domain is itself a scheme, so it needs to be
distilled. Then, we go under the binder and distill the codomain.

> distillScheme (l, ps) (SchExplicitPi (x :<: schS) schT) = do
>     -- Distill the domain
>     (schS', sty) <- distillScheme (l, ps) schS
>     -- Distill the codomain
>     (schT', tty) <- distillScheme (l+1, ps :< (l, x, sty)) schT
>     return (SchExplicitPi (x :<: schS') schT', partPiLift' (error "wook") (BV0 :<<<: (x, sty)) tty)

On an implicit $\Pi$, the operation is fairly similar. Instead of
|distillScheme|-ing the domain, we proceed as for ground types --- it
is one. 

> distillScheme (l, ps) (SchImplicitPi (x :<: s) schT) = do
>     -- Distill the domain
>     s' <- distill (SET :>: ev s) (l, ps)
>     -- Distill the codomain
>     (schT', t') <- distillScheme (l+1, ps :< (l, x, s)) schT
>     return (SchImplicitPi (x :<: s') schT', partPiLift' (error "wook") (BV0 :<<<: (x, s)) t')


\subsection{ProofState interface}

For ease of use, |distillScheme| is packaged specially for easy
ProofState usage.

> distillSchemePS :: Scheme -> ProofState DScheme
> distillSchemePS sch = do
>     lev <- getDevLev
>     fst <$> distillScheme (lev, B0) sch
>
> prettySchemePS :: Scheme -> ProofState Doc
> prettySchemePS sch = do
>     sch' <- distillSchemePS sch
>     return $ pretty sch' maxBound
