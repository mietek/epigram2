> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module Equality where

> import -> CanConstructors where
>   EqBlue :: (t :>: t) -> (t :>: t) -> Can t

> import -> CanPats where
>   pattern EQBLUE p q = C (EqBlue p q)

> import -> TraverseCan where
>   traverse f (EqBlue (pty :>: p) (qty :>: q)) =
>     (|EqBlue (|(:>:) (f pty) (f p)|) (|(:>:) (f qty) (f q)|)|)

> import -> CanTyRules where
>   canTy chev (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) = do
>     y0y0v@(y0 :=>: y0v) <- chev (SET :>: y0)
>     t0t0v@(t0 :=>: t0v) <- chev (y0v :>: t0)
>     y1y1v@(y1 :=>: y1v) <- chev (SET :>: y1)
>     t1t1v@(t1 :=>: t1v) <- chev (y1v :>: t1)
>     return $ EqBlue (y0y0v :>: t0t0v) (y1y1v :>: t1t1v)
>   canTy chev (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) = do
>     ppv@(p :=>: pv) <- chev (eqGreen @@ [y0, t0, y1, t1] :>: p)
>     return $ Con ppv

> import -> OpCode where
>   eqGreen = Op { opName = "eqGreen"
>                , opArity = 4
>                , opTy = opty
>                , opRun = opRunEqGreen
>                } where
>                opty chev [y0,t0,y1,t1] = do
>                    (y0 :=>: y0v) <- chev (SET :>: y0)
>                    (t0 :=>: t0v) <- chev (y0v :>: t0)
>                    (y1 :=>: y1v) <- chev (SET :>: y1)
>                    (t1 :=>: t1v) <- chev (y1v :>: t1)
>                    return ([ y0 :=>: y0v
>                            , t0 :=>: t0v
>                            , y1 :=>: y1v
>                            , t1 :=>: t1v ]
>                           , PROP)
>                opty _  _             = traceErr "eqGreen: invalid arguments."

>   coe = Op { opName = "coe"
>            , opArity = 4
>            , opTy = opty
>            , opRun = oprun
>            } where
>            opty chev [x,y,q,s] = do
>              (x :=>: xv) <- chev (SET :>: x)
>              (y :=>: yv) <- chev (SET :>: y)
>              (q :=>: qv) <- chev (PRF (EQBLUE (SET :>: xv) (SET :>: yv)) :>: q)
>              (s :=>: sv) <- chev (xv :>: s)
>              return ([ x :=>: xv
>                      , y :=>: yv
>                      , q :=>: qv
>                      , s :=>: sv ]
>                     , yv)
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
>            opty chev [x,y,q,s] = do
>              (x :=>: xv) <- chev (SET :>: x)
>              (y :=>: yv) <- chev (SET :>: y)
>              (q :=>: qv) <- chev (PRF (EQBLUE (SET :>: xv) (SET :>: yv)) :>: q)
>              (s :=>: sv) <- chev (xv :>: s)
>              return ([ x :=>: xv
>                      , y :=>: yv
>                      , q :=>: qv
>                      , s :=>: sv ]
>                     , PRF (EQBLUE (xv :>: sv) 
>                            (yv :>: coe @@ [xv,yv,qv,sv])))
>            oprun :: [VAL] -> Either NEU VAL
>            oprun [C x,C y,q,s] = Left undefined

> import -> Operators where
>   eqGreen :
>   coe :