> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module Evidences.TypeCheckRules where

> import Control.Applicative

> import Evidences.Tm

> canTy :: (Can, [EXP]) :>: Can -> Maybe VAL
> canTy ((Set, []) :>: Set)    = (| ONE |)
> canTy ((Set, []) :>: Pi)     = pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Sigma)  = pure $ ("S", SET) -** \ _S -> ARR _S SET *** ONE
> canTy ((Set, []) :>: Zero)   = (| ONE |)
> canTy ((Set, []) :>: One)    = (| ONE |)

> canTy ((Sigma, [_S, _T]) :>: Pair)  = pure $ ("s", _S) -** \ s -> wr _T s *** ONE
> canTy ((One, []) :>: Zero)          = (| ONE |)

> -- [Feature = Prop]
> canTy ((Set, []) :>: Prop)    = (| ONE |)
> canTy ((Set, []) :>: Prf)     = pure $ PROP *** ONE 
> canTy ((Prop, []) :>: Pi)     = pure $ ("S", SET) -** \ _S -> ARR _S PROP *** ONE
> canTy ((Prop, []) :>: Zero)   = (| ONE |)
> canTy ((Prop, []) :>: One)    = (| ONE |)
> canTy ((Prop, []) :>: Inh)    = pure $ SET *** ONE 
> canTy ((Prop, []) :>: And)    = pure $ PROP *** (PROP *** ONE)
> canTy ((Prf, [_P]) :>: p)     = case (ev _P, p) of
>   (ONE, Zero) -> (| ONE |)
>   (INH _T, Wit) -> pure $ _T *** ONE
>   (AND _P _Q, Pair) -> pure $ PRF _P *** (PRF _Q *** ONE)
> -- [/Feature = Prop]

> canTy _ = (|)
