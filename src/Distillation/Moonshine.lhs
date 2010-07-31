\section{The Moonshine distillery}
\label{sec:Distillation.Moonshine}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, TypeOperators, PatternGuards #-}

> module Distillation.Moonshine where

> import Control.Applicative
> import Data.Traversable

> import Kit.BwdFwd

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
\question{Presumably |moonshine| should accumulate |Entries| like
|distill| and friends?}

> moonshine :: INTM -> ProofStateT INTM DInTmRN
> moonshine (LK t) = do
>     t' <- moonshine t
>     return $ DLK t'
> moonshine (L (x :. t)) = do
>     t' <- moonshine t
>     return $ DL (x ::. t')
> moonshine (C c) = do
>     c' <- traverse moonshine c
>     return $ DC c'
> moonshine (N n) = (do
>     n' :<: ty <- distillInfer B0 n []
>     return $ DN n'
>   ) <|> return (DTIN (N n))
> moonshine t = return (DTIN t)


