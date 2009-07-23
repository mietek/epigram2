> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module Equality where

> import -> CanConstructors where
>   EqBlue :: (t :>: t) -> (t :>: t) -> Can t

> import -> CanPats where
>   pattern EQBLUE p q = C (EqBlue p q)

> import -> CanTyRules where
>   canTy ev (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) = Just $
>     EqBlue ((SET :>: y0) :>: (ev y0 :>: t0))
>            ((SET :>: y1) :>: (ev y1 :>: t1))
>   canTy ev (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) = Just $
>     Con (eqGreen @@ undefined :>: p)

> import -> OpCode where
>   eqGreen = Op { opName = "eqGreen"
>                , opArity = 4
>                , opTy = opty
>                , opRun = opRunEqGreen
>                } where
>                opty ev [y0,t0,y1,t1] = 
>                  Just ([SET :>: y0, ev y0 :>: t0,SET :>: y1,ev y1 :>: t1],
>                        PROP)
>                opty _  _             = Nothing

> import -> Operators where
>   eqGreen :