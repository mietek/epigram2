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
>   canTy ev (Set :>: Desc)     = return Desc
>   canTy ev (Set :>: Mu x)     = do
>     xv <- ev x
>     return $ Mu (DESC :>: x)
>   canTy ev (Desc :>: Done)    = return Done
>   canTy ev (Desc :>: Arg x y) = do
>     xv <- ev x
>     yv <- ev y
>     return $ Arg (SET :>: x)
>                  (ARR xv DESC :>: y) 
>   canTy ev (Desc :>: Ind x y) = do
>     xv <- ev x
>     yv <- ev y
>     return $ Ind (SET :>: x) (DESC :>: y)
>   canTy ev (Mu x :>: Intros y) = do
>     yv <- ev y
>     return $ Intros (descOp @@ [x, MU x] :>: y)

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "descOp"
>     , opArity = 2
>     , opTy = dOpTy
>     , opRun = dOpRun
>     } where
>       dOpTy chev [x,y] = do
>                  (x :=>: xv) <- chev (DESC :>: x)
>                  (y :=>: yv) <- chev (SET :>: y)
>                  return $ ([ x :=>: xv
>                            , y :=>: yv ]
>                           , SET)
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
>       boxOpTy chev [w,x,y,z] = do
>         (w :=>: wv) <- chev (DESC :>: w)
>         (x :=>: xv) <- chev (SET :>: x)
>         (y :=>: yv) <- chev (ARR xv SET :>: y)
>         (z :=>: zv) <- chev (descOp @@ [xv,yv] :>: z)
>         return ([ w :=>: wv
>                 , x :=>: xv
>                 , y :=>: yv
>                 , z :=>: zv ]
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

\pierre{Why |p| is ignored in the definition of |mapBoxOpTy|?}

>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBoxOp"
>     , opArity = 5
>     , opTy = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     } where
>       mapBoxOpTy chev [x,d,bp,p,v] = do 
>           (x :=>: xv) <- chev (DESC :>: x)
>           (d :=>: dv) <- chev (SET :>: d)
>           (bp :=>: bpv) <- chev (ARR dv SET :>: bp)
>           (v :=>: vv) <- chev (descOp @@ [xv,dv] :>: v)
>           -- chev on p?
>           return ([ x :=>: xv
>                   , d :=>: dv
>                   , bp :=>: bpv
>                   , v :=>: vv ]
>                  , boxOp @@ [xv,dv,bpv,vv])
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
>       elimOpTy chev [d,bp,p,v] = do
>         (d :=>: dv) <- chev (DESC :>: d)
>         (bp :=>: bpv) <- chev (ARR (MU dv) SET :>: bp)
>         (v :=>: vv) <- chev (MU dv :>: v)
>         (p :=>: pv) <- chev (ALL (descOp @@ [dv,MU dv]) 
>                     (eval [.d.bp.v. L $ "" :. [.x. 
>                         ARR (N (boxOp :@ [NV d,MU (NV d),NV bp,NV x]))
>                             (N (V bp :$ A (INTROS (NV x))))]
>                         ] $ B0 :< dv :< bpv :< vv) :>: p)
>         return ([ d :=>: dv
>                 , bp :=>: bpv
>                 , p :=>: pv
>                 , v :=>: vv ]
>                 , bpv $$ A vv)
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
