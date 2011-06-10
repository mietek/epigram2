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

> distillScheme :: [ EXP ] -> (Int, Bwd (Int, String, TY)) -> Scheme -> 
>                       ProofState (DScheme, TY)

On a ground type, there is not much to be done: |distill| does the
distillation job for us.

> distillScheme bs lps (SchType ty) = do
>     dty <- distill (SET :>: ev ty) lps
>     return (SchType dty, ty)

On an explicit $\Pi$, the domain is itself a scheme, so it needs to be
distilled. Then, we go under the binder and distill the codomain.

> distillScheme bs (l, ps) (SchExplicitPi (x :<: schS) schT) = do
>     -- Distill the domain
>     (schS', sty) <- distillScheme bs (l, ps) schS
>     -- Distill the codomain
>     (schT', tty) <- distillScheme bs (l+1, ps :< (l, x, sty)) schT
>     return (SchExplicitPi (x :<: schS') schT', piLift' (BV0 :<<<: (l, x, sty)) tty)

On an implicit $\Pi$, the operation is fairly similar. Instead of
|distillScheme|-ing the domain, we proceed as for ground types --- it
is one. 

> distillScheme bs (l, ps) (SchImplicitPi (x :<: s) schT) = do
>     -- Distill the domain
>     s' <- distill (SET :>: ev s) (l, ps)
>     -- Distill the codomain
>     (schT', t') <- distillScheme bs (l+1, ps :< (l, x, s)) schT
>     return (SchImplicitPi (x :<: s') schT', piLift' (BV0 :<<<: (l, x, s)) t')


\subsection{ProofState interface}

For ease of use, |distillScheme| is packaged specially for easy
ProofState usage.

> distillSchemePS :: Scheme -> ProofState DScheme
> distillSchemePS sch = do
>     lev <- getDevLev
>     es <- getInScope
>     fst <$> distillScheme (boys es []) (lev, B0) sch
>   where boys B0 bs = bs
>         boys (es :< EParam k s t l) bs = boys es ((P (l, s, t) :$ B0) : bs)
>         boys (es :< _) bs = boys es bs
>
> prettySchemePS :: Scheme -> ProofState Doc
> prettySchemePS sch = do
>     sch' <- distillSchemePS sch
>     return $ pretty sch' maxBound
