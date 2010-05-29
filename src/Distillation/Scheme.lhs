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

> import DisplayLang.Scheme
> import DisplayLang.Name
> import DisplayLang.PrettyPrint

> import NameSupply.NameSupplier

> import Evidences.Rules
> import Evidences.Tm
> import Evidences.Mangler

%endif


\subsection{Distilling Schemes}



> distillScheme ::  Entries -> Bwd REF -> Scheme INTM -> 
>                   ProofStateT INTM (Scheme DInTmRN, INTM)

> distillScheme es rs (SchType ty) = do
>     let ty' = underneath 0 rs ty
>     ty'' :=>: _ <- distill es (SET :>: ty')
>     return (SchType ty'', ty')

> distillScheme es rs (SchExplicitPi (x :<: schS) schT) = do
>     (schS', s') <- distillScheme es rs schS
>     freshRef (x :<: evTm s')(\ref -> do
>         (schT', t') <- distillScheme (es :< E ref (lastName ref) (Boy PIB) s')
>                            (rs :< ref) schT
>         return (SchExplicitPi (x :<: schS') schT', PIV x s' t')
>       )

> distillScheme es rs (SchImplicitPi (x :<: s) schT) = do
>     let s' = underneath 0 rs s
>     sd :=>: sv <- distill es (SET :>: s')
>     freshRef (x :<: sv) (\ref -> do
>         (schT', t') <- distillScheme (es :< E ref (lastName ref) (Boy PIB) s')
>                            (rs :< ref) schT
>         return (SchImplicitPi (x :<: sd) schT', PIV x s' t')
>       )


> underneath :: Int -> Bwd REF -> INTM -> INTM
> underneath _ B0 tm = tm
> underneath n (rs :< ref) tm = underneath (n+1) rs (under n ref %% tm)


\subsection{ProofState interface}

> distillSchemeHere :: Scheme INTM -> ProofState (Scheme DInTmRN)
> distillSchemeHere sch = do
>     return . fst =<< (mapStateT liftError $ distillScheme B0 B0 sch)


> prettySchemeHere :: Scheme INTM -> ProofState Doc
> prettySchemeHere sch = do
>     sch' <- distillSchemeHere sch
>     return (pretty sch' maxBound)
