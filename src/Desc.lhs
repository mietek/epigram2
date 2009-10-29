> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Desc where

> import -> CanConstructors where
>   Desc   :: Can t
>   Mu     :: t -> Can t
>   Done   :: Can t
>   Arg    :: t -> t -> Can t
>   Ind    :: t -> t -> Can t
>   Intros :: t -> Can t

> import -> TraverseCan where
>   traverse _ Desc       = (|Desc|)
>   traverse f (Mu x)     = (|Mu (f x)|)
>   traverse _ Done       = (|Done|)
>   traverse f (Arg x y)  = (|Arg (f x) (f y)|)
>   traverse f (Ind x y)  = (|Ind (f x) (f y)|)
>   traverse f (Intros x) = (|Intros (f x)|)

> import -> CanPats where
>   pattern DESC     = C Desc
>   pattern MU x     = C (Mu x)
>   pattern DONE     = C Done
>   pattern ARG x y  = C (Arg x y)
>   pattern IND x y  = C (Ind x y)
>   pattern INTROS x = C (Intros x)

> import -> CanTyRules where
>   canTy tc (Set :>: Desc)     = Just Desc
>   canTy tc (Set :>: Mu x)     = DESC `tc` x &\ \ x _ -> Just (Mu x)
>   canTy tc (Desc :>: Done)    = Just Done
>   canTy tc (Desc :>: Arg x y) = 
>     SET `tc` x &\ \ x xv -> 
>     ARR xv DESC `tc` y &\ \ y _ -> Just (Arg x y)
>   canTy tc (Desc :>: Ind x y) =
>     SET `tc` x &\ \ x _ ->
>     DESC `tc` y &\ \ y _ -> Just (Ind x y)
>   canTy tc (Mu x :>: Intros y) =
>     descOp @@ [x, MU x] `tc` y &\ \ t _ -> Just (Intros t)

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "descOp"
>     , opArity = 1
>     , opTy = dOpTy
>     , opRun = dOpRun
>     } where
>       dOpTy ev [x,y] = Just ([DESC :>: x,SET :>: y],SET)
>       dOpRun :: [VAL] -> Either NEU VAL
>       dOpRun [DONE,y]    = Right UNIT
>       dOpRun [ARG x y,z] = Right $
>         eval [.x.y.z. 
>              SIGMA (NV x) . L $ "" :. [.a.
>              (N (descOp :@ [y $# [a],NV z]))
>              ]] $ B0 :< x :< y :< z

>       dOpRun [IND x y,z] = Right (TIMES (ARR x z) (descOp @@ [y,z]))
>       dOpRun [N x,_]     = Left x

>   boxOp :: Op
>   boxOp = Op
>     { opName = "boxOp"
>     , opArity = 4
>     , opTy = boxOpTy
>     , opRun = boxOpRun
>     } where
>       boxOpTy ev [w,x,y,z] = 
>         Just ([DESC :>: w,
>                SET :>: x,
>                ARR (ev x) SET :>: y,
>                descOp @@ [ev x,ev y] :>: z]
>                , SET)
>       boxOpRun :: [VAL] -> Either NEU VAL
>       boxOpRun [DONE   ,d,p,v] = Right UNIT
>       boxOpRun [ARG a f,d,p,v] = Right $
>         boxOp @@ [f $$ A (v $$ Fst),d,p,v $$ Snd] 
>       boxOpRun [IND h x,d,p,v] = Right $
>         eval [.h.x.d.p.v.
>              TIMES (ALL (NV h) . L $ "" :. [.y.
>                                    N (V p :$ A (N (V v :$ Fst :$ A (NV h))))])
>                   (N (boxOp :@ [NV x,NV d,NV p,N (V v :$ Snd)]))
>              ] $ B0 :< h :< x :< d :< p :< v
>       boxOpRun [N x    ,_,_,_] = Left x

>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBoxOp"
>     , opArity = 5
>     , opTy = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     } where
>       mapBoxOpTy ev [x,d,bp,p,v] = Just $
>         ([DESC :>: x
>          ,SET :>: d
>          ,ARR (ev d) SET :>: bp
>          ,descOp @@ [ev x,ev d] :>: v]
>         ,boxOp @@ [ev x,ev d,ev bp,ev v])
>       mapBoxOpRun :: [VAL] -> Either NEU VAL
>       mapBoxOpRun [DONE,d,bp,p,v] = Right VOID
>       mapBoxOpRun [ARG a f,d,bp,p,v] = Right $
>         mapBoxOp @@ [f $$ (A (v $$ Fst)),d,bp,p,v $$ Snd]
>       mapBoxOpRun [IND h x,d,bp,p,v] = Right $
>         eval [.h.x.d.bp.p.v.
>              PAIR (L $ "" :. [.y. N (V p :$ A (N (V v :$ Fst :$ A (NV y))))])
>                   (N (mapBoxOp :@ [NV x,NV d
>                                   ,NV bp
>                                   ,NV p
>                                   ,N (V p :$ A (N (V v :$ Snd)))
>                                   ]))
>              ] $ B0 :< h :< x :< d :< bp :< p :< v
>       mapBoxOpRun [N x    ,_, _,_,_] = Left x
 
>   elimOp :: Op
>   elimOp = Op
>     { opName = "elimOp"
>     , opArity = 4
>     , opTy = elimOpTy
>     , opRun = elimOpRun
>     } where
>       elimOpTy ev [d,bp,p,v] = Just $
>              ([DESC :>: d
>              ,ARR (MU (ev d)) SET :>: bp
>              ,ALL (descOp @@ [ev d,MU (ev d)]) 
>                   (eval [.d.bp.p.v. L $ "" :. [.x. 
>                         ARR (N (boxOp :@ [NV d,MU (NV d),NV bp,NV x]))
>                             (N (V bp :$ A (INTROS (NV x))))]
>                         ] $ B0 :< ev d :< ev bp :< ev p :< ev v) :>: p
>              ,MU (ev d):>: v
>              ], ev bp $$ A (ev v))

>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [d,bp,p,INTROS v] = Right $
>          p $$ A v $$ A (mapBoxOp @@ 
>                         [d
>                         ,MU d
>                         ,bp
>                         ,eval [.d.bp.p. L $ "" :. [.x. 
>                               N (elimOp :@ [NV d,NV bp,NV p,NV x])]
>                               ] $ B0 :< d :< bp :< p
>                         ,v])
>       elimOpRun [_, _,_,N x] = Left x
