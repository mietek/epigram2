> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module Equality where

> import -> CanConstructors where
>   EqBlue :: (t :>: t) -> (t :>: t) -> Can t

> import -> CanPats where
>   pattern EQBLUE p q = C (EqBlue p q)

> import -> CanTyRules where
>   canTy tc (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) =
>     SET `tc` y0 &\ \ y0 y0v ->
>     y0v `tc` t0 &\ \ t0 _ ->
>     SET `tc` y1 &\ \ y1 y1v ->
>     y1v `tc` t1 &\ \ t1 _ ->
>     Just $ EqBlue (y0 :>: t0) (y1 :>: t1)
>   canTy tc (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) =
>     (eqGreen @@ [y0, t0, y1, t1]) `tc` p &\ \ p _ ->
>     Just $ Con p

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

>   coe = Op { opName = "coe"
>            , opArity = 4
>            , opTy = opty
>            , opRun = oprun
>            } where
>            opty ev [x,y,q,s] = 
>              Just ([ SET :>: x
>                    , SET :>: y
>                    , PRF (EQBLUE (SET :>: ev x) (SET :>: ev y)) :>: q
>                    , ev x :>: s
>                    ],ev y)
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [C x,C y,q,s] = Right $ case halfZip x y of
>              Nothing  -> ABSURD
>              Just fxy -> coerce fxy q s
>            oprun [N x,y,q,s] = Left x
>            oprun [x,N y,q,s] = Left y
>            oprun _ = undefined
>
>   coh = Op { opName = "coh"
>            , opArity = 4
>            , opTy = opty
>            , opRun = oprun
>            } where
>            opty ev [x,y,q,s] =
>              Just ([SET :>: x,
>                     SET :>: y,
>                     PRF (EQBLUE (SET :>: ev x) (SET :>: ev y)) :>: q,
>                     ev x :>: s],
>                     PRF (EQBLUE (ev x :>: ev s) 
>                                 (ev y :>: coe @@ [ev x,ev y,ev q,ev s])))
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [C x,C y,q,s] = Left undefined

> import -> Operators where
>   eqGreen :
>   coe :