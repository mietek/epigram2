> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module Evidences.TypeCheckRules where

> import Control.Applicative

> import Evidences.Tm

> canTy :: (Can, [EXP]) :>: Can -> Maybe VAL
> canTy ((Set, []) :>: Set)    = (| ONE |)
> canTy ((Set, []) :>: Pi)     = pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Sigma)  = pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: One)    = (| ONE |)
> canTy ((Set, []) :>: Zero)   = (| ONE |)

> canTy ((Sigma, [_S, _T]) :>: Pair)  = pure $ ("s", _S) -** \ s -> wr _T s *** ONE
> canTy ((One, []) :>: Zero)          = (| ONE |)
> canTy _ = (|)
