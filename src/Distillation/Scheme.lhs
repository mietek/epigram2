\section{The Scheme distiller}
\label{sec:scheme-distiller}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Scheme where

> import Control.Monad.State
> import Text.PrettyPrint.HughesPJ (Doc)

> import Kit.BwdFwd

> import ProofState.Developments
> import ProofState.ProofState

> import Distillation.Distiller

> import DisplayLang.DisplayTm
> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import NameSupply.NameSupplier

> import Evidences.Rules
> import Evidences.Tm
> import Evidences.Mangler

%endif


\subsection{Distilling schemes}

Distilling a scheme is similar in spirit to distilling a
$\lambda$-abstraction (Section~\ref{subsec:distiller-int}). Provided a
|Scheme INTM|, we compute the same scheme structure, with Display
terms instead.

To do so, we proceed structurally, using |distill| on types and,
recursively, |distillScheme| on schemes. Each time we go through a
$\Pi$, we go under a binder; therefore we need to be careful to turn
freshly introduced references back into De Bruijn indices.

This distiller takes the list of local entries we are working under,
as well as the collected list of references we have made so far. It
turns the |INTM| scheme into an a Display term scheme with relative
names.

> distillScheme ::  Entries -> Bwd REF -> Scheme INTM -> 
>                   ProofStateT INTM (Scheme DInTmRN, INTM)

On a ground type, there is not much to be done: |distill| does the
distillation job for us. However, we first have to discharge the fresh
|refs| back.

> distillScheme entries refs (SchType ty) = do
>     -- Discharge |refs|
>     let ty1 = underneath refs ty
>     -- Distill the type
>     ty2 :=>: _ <- distill entries (SET :>: ty1)
>     return (SchType ty2, ty1)

On an explicit $\Pi$, the domain is itself a scheme, so it needs to be
distilled. Then, we go under the binder and distill the codomain,
carrying the new |ref| and extending the local entries with it.

\pierre{Why extending |entries|?}

> distillScheme entries refs (SchExplicitPi (x :<: schS) schT) = do
>     -- Distill the domain
>     (schS', s') <- distillScheme entries refs schS
>     -- Under a fresh |ref|\ldots
>     freshRef (x :<: evTm s') $ \ref -> do
>         -- Distill the codomain
>         (schT', t') <- distillScheme  
>                          (entries :< E ref (lastName ref) (Boy PIB) s')
>                          (refs :< ref) 
>                          schT
>         return (SchExplicitPi (x :<: schS') schT', PIV x s' t')

On an implicit $\Pi$, the operation is fairly similar. Instead of
|distillScheme|-ing the domain, we proceed as for ground types -- it
is one. 

> distillScheme entries refs (SchImplicitPi (x :<: s) schT) = do
>     -- Distill the domain as a ground type
>     let s' = underneath refs s
>     sd :=>: sv <- distill entries (SET :>: s')
>     -- Under a fresh |ref|\ldots
>     freshRef (x :<: sv) $ \ref -> do
>         -- Distill the domain
>         (schT', t') <- distillScheme 
>                          (entries :< E ref (lastName ref) (Boy PIB) s')
>                          (refs :< ref) 
>                          schT
>         return (SchImplicitPi (x :<: sd) schT', PIV x s' t')


We have been helped by |underneath| to discharge the fresh references
into the terms.

> underneath :: Bwd REF -> INTM -> INTM
> underneath = underneath' 0 
>     where 
>       underneath' :: Int -> Bwd REF -> INTM -> INTM
>       underneath' _ B0          tm = tm
>       underneath' n (rs :< ref) tm = underneath' (n+1) rs (under n ref %% tm)


\subsection{ProofState interface}

For ease of use, |distillScheme| is packaged specially for easy
ProofState usage.

> distillSchemeHere :: Scheme INTM -> ProofState (Scheme DInTmRN)
> distillSchemeHere sch = do
>     return . fst =<< (liftErrorState DTIN $ distillScheme B0 B0 sch)
>
> prettySchemeHere :: Scheme INTM -> ProofState Doc
> prettySchemeHere sch = do
>     sch' <- distillSchemeHere sch
>     return $ pretty sch' maxBound
