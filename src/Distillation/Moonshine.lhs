\section{The Moonshine distillery}
\label{sec:Distillation.Moonshine}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards, FlexibleContexts #-}

> module Distillation.Moonshine where

> import Control.Applicative
> import Control.Monad.Error
> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import ProofState.Edition.ProofState

> import Distillation.Distiller

> import DisplayLang.DisplayTm
> import DisplayLang.Name

> import Evidences.Tm

%endif


\subsection{Moonshining}

The |moonshine| command attempts the dubious task of converting an
Evidence term (possibly of dubious veracity) into a Display term.
This is mostly for error-message generation.

> moonshine' :: Int -> Bwd (Int, String, TY) -> EXP -> ProofState DInTmRN
> moonshine' l es (LK t) = do
>     t' <- moonshine' l es t
>     return $ DLK t'
> moonshine' l es (L g x t) = do
>     t' <- moonshine' (l + 1) (es :< (l, x, error "MOONSHINE")) 
>            ((g <:< (P (l, x, error "MOOONSHINE") :$ B0)) // t)
>     return $ DL (x ::. t')
> moonshine' l es (c :- as) = do
>     as' <- traverse (moonshine' l es) as
>     return $ DC c as'
> moonshine' l es n@(f :$ as) = (do
>     (f', ty, ss, ms) <- distillHead f (trail as) (l,es)
>     as' <- distillSpine (ev ty :>: (ev f , ss, ms)) (l, es)
>     return $ DN (f' ::$ as')
>   ) `catchError` \_ -> return (DTIN n)
> moonshine' l es t = return (DTIN t)

> moonshine :: EXP -> ProofState DInTmRN
> moonshine = moonshine' 0 B0
