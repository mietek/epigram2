\section{The Scheme distiller}
\label{sec:Distillation.Scheme}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Scheme where

> import Text.PrettyPrint.HughesPJ (Doc)

> import Kit.BwdFwd

> import ProofState.Structure.Developments
> import ProofState.Edition.ProofState

> import Distillation.Distiller

> import DisplayLang.DisplayTm
> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import NameSupply.NameSupplier

> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval

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

> distillScheme ::  Entries -> Bwd REF -> Scheme INTM -> 
>                   ProofStateT INTM (Scheme DInTmRN, INTM)

On a ground type, there is not much to be done: |distill| does the
distillation job for us. However, we first have to turn the
de Bruijn indices into references.

> distillScheme entries refs (SchType ty) = do
>     -- Instantiate de Bruijn indices with |refs|
>     let ty1 = underneath refs ty
>     -- Distill the type
>     ty2 :=>: _ <- distill entries (SET :>: ty1)
>     return (SchType ty2, ty1)

On an explicit $\Pi$, the domain is itself a scheme, so it needs to be
distilled. Then, we go under the binder and distill the codomain,
carrying the new |ref| and extending the local entries with it.
The new reference is in local scope, so we need to extend the entries
with it for later distillation. We know the |INTM| form of its type so
we may as well supply it, though it should not be inspected.

> distillScheme entries refs (SchExplicitPi (x :<: schS) schT) = do
>     -- Distill the domain
>     (schS', s') <- distillScheme entries refs schS
>     -- Under a fresh |ref|\ldots
>     freshRef (x :<: evTm s') $ \ref -> do
>         -- Distill the codomain
>         (schT', t') <- distillScheme  
>                          (entries :< EPARAM ref (mkLastName ref) ParamPi s' Nothing)
>                          (refs :< ref) 
>                          schT
>         return (SchExplicitPi (x :<: schS') schT', PIV x s' t')

On an implicit $\Pi$, the operation is fairly similar. Instead of
|distillScheme|-ing the domain, we proceed as for ground types --- it
is one. 

> distillScheme entries refs (SchImplicitPi (x :<: s) schT) = do
>     -- Distill the domain as a ground type
>     let s' = underneath refs s
>     sd :=>: sv <- distill entries (SET :>: s')
>     -- Under a fresh |ref|\ldots
>     freshRef (x :<: sv) $ \ref -> do
>         -- Distill the domain
>         (schT', t') <- distillScheme 
>                          (entries :< EPARAM ref (mkLastName ref) ParamPi s' Nothing)
>                          (refs :< ref) 
>                          schT
>         return (SchImplicitPi (x :<: sd) schT', PIV x s' t')


We have been helped by |underneath|, which replaces (de Bruijn indexed)
variables in a term with references from the given list.

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
