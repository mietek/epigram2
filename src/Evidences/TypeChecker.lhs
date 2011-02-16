\section{Type-checker}
\label{sec:Evidences.TypeChecker}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, FlexibleContexts, PatternGuards #-}

> module Evidences.TypeChecker where

> import Prelude hiding (exp)

> import Control.Applicative
> import Control.Monad.Error

> import Data.Traversable

> import Kit.BwdFwd
> import Kit.MissingLibrary

> import Evidences.Tm
> import Evidences.TmJig
> import Evidences.NameSupply

%endif


> canTy :: (Can, [EXP]) :>: Can -> Maybe VAL
> canTy ((Set, []) :>: Set)    = return ONE
> canTy ((Set, []) :>: Pi)     = return $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Sigma)  = return $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: One)    = return ONE

> canTy ((Sigma, [_S, _T]) :>: Pair)  = return $ ("s", _S) -** \ s -> wr _T s *** ONE
> canTy ((One, []) :>: Zero)          = return ONE








