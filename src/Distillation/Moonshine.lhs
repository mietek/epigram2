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

> moonshine :: Int -> EXP -> ProofState DInTmRN
> moonshine l (LK t) = do
>     t' <- moonshine l t
>     return $ DLK t'
> moonshine l (L g x t) = do
>     t' <- moonshine (l + 1) ((g <:< (P (l, x, error "MOOONSHINE") :$ B0)) // t)
>     return $ DL (x ::. t')
> moonshine l (c :- as) = do
>     as' <- traverse (moonshine l) as
>     return $ DC c as'
> moonshine l n@(f :$ as) = (do
>     (f', ty, ss) <- distillHead f
>     as' <- distillSpine (ev ty :>: (ev f , ss ++ trail as)) l
>     return $ DN (f' ::$ as')
>   ) `catchError` \_ -> return (DTIN n)
> moonshine l d@(D _ _ _) = (do
>     (f', ty, ss) <- distillHead d
>     as' <- distillSpine (ev ty :>: (ev d , ss)) l
>     return $ DN (f' ::$ as')
>   ) `catchError` \_ -> return (DTIN d)
> moonshine l t = return (DTIN t)

