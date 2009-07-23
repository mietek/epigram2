\section{Containers}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Containers where

%endif

> import -> CanConstructors where
>   ContU   :: t -> Can t
>   ReqC    :: t -> Can t
>   UnitC   :: Can t 
>   TimesC  :: t -> t -> Can t 
>   PiC     :: t -> t -> Can t
>   SigmaC  :: t -> t -> Can t
>   MuC     :: t -> t -> t -> Can t
>   NuC     :: t -> t -> t -> Can t
>   Mu      :: t -> t -> t -> t -> t -> Can t
>   Nu      :: t -> t -> t -> t -> t -> Can t

> -- import -> ElimComputation where

> import -> TraverseCan where
>   traverse f (ContU i)        = (|ContU (f i)|)
>   traverse f (ReqC i)         = (|ReqC (f i)|)
>   traverse f UnitC            = (|UnitC|)
>   traverse f (TimesC x y)     = (|TimesC (f x) (f y)|)
>   traverse f (SigmaC s t)     = (|SigmaC (f s) (f t)|)
>   traverse f (PiC s t)        = (|PiC (f s) (f t)|)
>   traverse f (MuC o x oi)     = (|MuC (f o) (f x) (f oi)|) 
>   traverse f (NuC o x oi)     = (|NuC (f o) (f x) (f oi)|) 
>   traverse f (Mu i o d x oi)  = (|Mu (f i) (f o) (f d) (f x) (f oi)|) 
>   traverse f (Nu i o d x oi)  = (|Nu (f i) (f o) (f d) (f x) (f oi)|) 


> -- import -> TraverseElim where

> import -> CanPats where
>   pattern CONTU i        = C (ContU i)
>   pattern REQC i         = C (ReqC i)
>   pattern UNITC          = C UnitC
>   pattern TIMESC x y     = C (TimesC x y)
>   pattern SIGMAC s t     = C (SigmaC s t)
>   pattern PIC s t        = C (PiC s t)
>   pattern MUC o x oi     = C (MuC o x oi)
>   pattern NUC o x oi     = C (NuC o x oi)
>   pattern MU i o d x oi  = C (Mu i o d x oi)
>   pattern NU i o d x oi  = C (Nu i o d x oi)

> import -> CanTyRules where
>   -- ContU Rules :
>   canTy ev (Set :>: ContU i) = Just (ContU (SET :>: i))
>       where vi = ev i
>   canTy ev (ContU i :>: ReqC ii) = Just (ReqC (i :>: ii))
>   canTy ev (ContU i :>: UnitC) = Just UnitC
>   canTy ev (ContU i :>: TimesC x y) = 
>     Just (TimesC (CONTU i :>: x) (CONTU i :>: y))
>   canTy ev (ContU i :>: SigmaC s t) = 
>     Just (SigmaC (SET :>: s) (Arr (ev s) (CONTU i) :>: t))
>   canTy ev (ContU i :>: PiC s t) = 
>     Just (PiC (SET :>: s) (Arr (ev s) (CONTU i) :>: t))
>   canTy ev (ContU i :>: MuC o x oi) = 
>     Just (MuC (SET :>: o) (Arr ov (CONTU (sumVV i ov)) :>: x) (ov :>: oi))
>       where ov = ev o 
>   canTy ev (ContU i :>: NuC o x oi) = 
>     Just (NuC (SET :>: o) (Arr ov (CONTU (sumVV i ov)) :>: x) (ov :>: oi))
>       where ov = ev o 
>   -- Mu, Nu Rules
>   canTy ev (Set :>: Mu i o d x oi) = 
>     Just (Mu (SET :>: i) (SET :>: o) 
>          (Arr ov (CONTU (sumVV (ev i) ov)) :>: d)
>          (Arr ov SET :>: x) (ov :>: oi)) 
>       where ov = ev o
>   canTy ev (Set :>: Nu i o d x oi) = 
>     Just (Nu (SET :>: i) (SET :>: o) 
>          (Arr ov (CONTU (sumVV (ev i) ov)) :>: d)
>          (Arr ov SET :>: x) (ov :>: oi))
>       where ov = ev o
>   canTy ev (Mu i o d x oi :>: Con t) = 
>     Just (Con (contTOp @@ [ i 
>                           , d $$ A o  
>                           , cases (L (K SET)) x 
>                                     (L (H (bwdList [i,o,d,x]) "" 
>                                           (MU (NV 4) (NV 3) 
>                                               (NV 2) (NV 1) (NV 0))))
>                          ] :>: t))
>   canTy ev (Nu i o d x oi :>: Con t) = 
>     Just (Con (contTOp @@ [ i 
>                           , d $$ A o  
>                           , cases (L (K SET)) x 
>                                     (L (H (bwdList [i,o,d,x]) "" 
>                                           (MU (NV 4) (NV 3) 
>                                               (NV 2) (NV 1) (NV 0))))
>                           ] :>: t))

> import -> OpCode where
>   boolE :: Tm {In,p} x
>   boolE = (CONSE (TAG "ff") (CONSE (TAG "tt") NILE))
>
>   boolT :: Tm {In,p} x
>   boolT = ENUMT boolE
>
>   sumVV :: VAL -> VAL -> VAL
>   sumVV x y = 
>     SIGMA boolT 
>           (L (H (B0 :< x :< y) "b" (SIGMA (N (switchOp :@ [ boolE 
>                                                           , L (K SET)
>                                                           , PAIR (NV 2) 
>                                                              (PAIR (NV 1) 
>                                                                VOID)  
>                                                           , NV 0]))
>                                           (L (K UNIT)))))
>
>   cases :: VAL -> VAL -> VAL -> VAL
>   cases dty f g = 
>     L (H (B0 :< dty :< f :< g) "" 
>          (N (switchOp :@ 
>               [ boolE
>               , N (V 3)
>               , PAIR (N ((V 2) :$ A (N (V 0 :$ Snd :$ Fst))))  
>                   (PAIR (N ((V 1) :$ A (N (V 0 :$ Snd :$ Fst)))) VOID)  
>               , N ((V 0) :$ Fst) ])))
> 
>   contTOp :: Op
>   contTOp = Op
>     { opName = "cont"
>     , opArity = 3
>     , opTy = cTOpTy
>     , opRun = cTOpRun
>     } where
>         cTOpTy ev [i , c , x] = 
>           Just ([ SET :>: i , CONTU vi :>: c , Arr vi SET :>: x ] , SET)
>             where vi = ev i 
>         cTOpTy _ _ = Nothing
>         cTOpRun :: [VAL] -> Either NEU VAL
>         cTOpRun [i , REQC ii , x] = Right (x $$ (A ii))
>         cTOpRun [i , UNITC , x] = Right UNIT
>         cTOpRun [i , TIMESC a b , x] = Right (TIMES a b)
>         cTOpRun [i , SIGMAC a b , x] = Right $
>           SIGMA a (L (H (B0 :< i :< b :< x) "" 
>                    (N (contTOp :@ [NV 3 , N ((V 2) :$ A (NV 0)) , NV 1 ]))))
>         cTOpRun [i , PIC a b , x] = Right $ C $
>           Pi a (L (H (B0 :< i :< b :< x) "" 
>                 (N (contTOp :@ [NV 3 , N ((V 2) :$ A (NV 0)) , NV 1 ]))))
>         cTOpRun [i , MUC o c oi , x] = Right (MU i o c x oi)
>         cTOpRun [i , NUC o c oi , x] = Right (NU i o c x oi)
>         cTOpRun [i , N c , x] = Left c
>
>   mapCOp :: Op
>   mapCOp = Op 
>     { opName = "mapC"
>     , opArity = 5
>     , opTy = mOpTy
>     , opRun = mOpRun
>     } where
>       mOpTy ev [i , c , x , y , f , t] = Just $
>         ([ SET :>: i , CONTU (ev i) :>: c 
>          , Arr vi SET :>: x , Arr vi SET :>: y
>          , C (Pi vi (L (H (B0 :< vx :< vy) "" 
>                     (Arr (N (V 2 :$ A (NV 0))) (N (V 1 :$ A (NV 0)))))))
>              :>: f
>          , contTOp @@ [ vi , vc , vx ] :>: t ] , contTOp @@ [ vi , vc , vy ])
>             where vi = ev i
>                   vc = ev c
>                   vx = ev x 
>                   vy = ev y 
>       mOpRun :: [VAL] -> Either NEU VAL
>       mOpRun [i , REQC ii , x , y , f , t] = Right $ f $$ A ii $$ A t
>       mOpRun [i , UNITC , x , y , f , t] = Right $ VOID
>       mOpRun [i , TIMESC a b , x , y , f , t] = Right $ 
>         PAIR (mapCOp @@ [i , a , x , y , f , t $$ Fst])
>              (mapCOp @@ [i , b , x , y , f , t $$ Snd]) 
>       mOpRun [i , SIGMAC a b , x , y , f , t] = let t0 = t $$ Fst in Right $
>         PAIR t0 (mapCOp @@ [i , b $$ A t0 , x , y , f , t $$ Snd])
>       mOpRun [i , PIC a b , x , y , f , t] = Right $
>         L (H (bwdList [i , b , x , y , f , t]) ""
>              (N (mapCOp :@ [ N (V 6) , N (V 5 :$ A (N (V 0))) , N (V 4)
>                            , N (V 3) , N (V 2) , N (V 1 :$ A (N (V 0))) ])))
>       mOpRun [i , MUC o c oi , x , y , f , CON t] = Right $
>         CON (mapCOp @@ 
>               [ sumVV i o , c $$ A oi , x' , y'
>               , cases (L (H (B0 :< x' :< y') "" 
>                         (Arr (N (V 2 :$ A (NV 0))) 
>                              (N (V 1 :$ A (NV 0)))))) 
>                       f 
>                       (L (H (bwdList [i , o , c , x , y , f]) "" 
>                         (L ("" :. 
>                           (N (mapCOp :@ [ NV 7  
>                                         , MUC (NV 6) (NV 5) (NV 1) 
>                                         , NV 4 , NV 3 , NV 2 
>                                         , NV 0 ]))))))
>               , t ])  
>           where 
>             x' = cases (L (K SET)) x 
>                          (L (H (B0 :< i :< c) "" 
>                               (N (contTOp :@ [ NV 2 , NV 1 , NV 0 ]))))
>             y' = cases (L (K SET)) y 
>                          (L (H (B0 :< i :< c) "" 
>                               (N (contTOp :@ [ NV 2 , NV 1 , NV 0]))))
>       mOpRun [i , NUC o c oi , x , y , f , t] = Right $ undefined
>       mOpRun [i , N c , x , y , f , t] = Left c 
>       mOpRun [i , c , x , y , f , N t] = Left t 

> import -> Operators where
>   contTOp :
>   mapCOp :
>   

> -- import -> ElimTyRules where

> -- import -> EtaExpand where
