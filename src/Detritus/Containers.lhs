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

> import -> DisplayCanPats where
>   pattern DCONTU i        = DC (ContU i)
>   pattern DREQC i         = DC (ReqC i)
>   pattern DUNITC          = DC UnitC
>   pattern DTIMESC x y     = DC (TimesC x y)
>   pattern DSIGMAC s t     = DC (SigmaC s t)
>   pattern DPIC s t        = DC (PiC s t)
>   pattern DMUC o x oi     = DC (MuC o x oi)
>   pattern DNUC o x oi     = DC (NuC o x oi)
>   pattern DMU i o d x oi  = DC (Mu i o d x oi)
>   pattern DNU i o d x oi  = DC (Nu i o d x oi)

> import -> CanTyRules where
>   -- ContU Rules :
>   canTy ev (Set :>: ContU i) = do
>     iv <- ev i
>     return $ ContU (SET :>: i)
>   canTy ev (ContU i :>: ReqC ii) = do
>     iiv <- ev ii
>     return $ ReqC (i :>: ii)
>   canTy _ (ContU i :>: UnitC) = return (i :>: UnitC)
>   canTy ev (ContU i :>: TimesC x y) = do
>     xv <- ev x
>     yv <- ev y
>     return $ TimesC (CONTU i :>: x) (CONTU i :>: y)
>   canTy ev (ContU i :>: SigmaC s t) = do
>     sv <- ev s
>     tv <- ev t
>     return $ SigmaC (SET :>: s) (ARR sv (CONTU i) :>: t)
>   canTy ev (ContU i :>: PiC s t) = do
>     sv <- ev s
>     tv <- ev t
>     return $ PiC (SET :>: s) (CONTU :>: t)
>   canTy ev (ContU i :>: MuC o x oi) = do
>     ov <- ev o
>     xv <- ev x
>     oiv <- ev oi
>     return $ MuC (SET :>: o) 
>                  (ARR ov (CONTU (sumVV $$ A i $$ A ov)) :>: x)
>                  (ov :>: oi)
>   canTy ev (ContU i :>: NuC o x oi) = do
>     ov <- ev o
>     xv <- ev x
>     oiv <- ev oi
>     return $ NuC (SET :>: o)
>                  (ARR ov (CONTU (sumVV $$ A i $$ A ov)) :>: x)
>                  (ov :>: oi)
>   -- Mu, Nu Rules
>   canTy ev (Set :>: Mu i o d x oi) = do
>     iv <- ev i
>     ov <- ev o
>     dv <- ev d
>     oiv <- ev oi
>     return $ Mu (SET :>: i)
>                 (SET :>: o)
>                 (ARR ov (CONTU (sumVV $$ A iv $$ A ov)) :>: d)
>                 (ARR iv SET :>: x)
>                 (ov :>: oi)
>   canTy ev (Set :>: Nu i o d x oi) = do
>     iv <- ev i
>     ov <- ev o
>     dv <- ev d
>     xv <- ev x
>     oiv <- ev oi
>     return $ Nu (SET :>: i)
>                 (SET :>: o)
>                 (ARR ov (CONTU (sumVV $$ A iv $$ A ov)) :>: d)
>                 (ARR iv SET :>: x)
>                 (ov :>: oi)
>   canTy ev (Mu i o d x oi :>: Con t) = do
>     tv <- ev t
>     return $ Con (contTOp @@  [ i 
>                               , d $$ A o  
>                               , L (H (bwdList [i,o,d,x]) "t"
>                                          (N (casesOp :@ 
>                                              [ NV 4 , NV 3
>                                              , L (K SET) , NV 1  
>                                              , L ("oo" :. (MU (NV 5) (NV 4) 
>                                                            (NV 3) (NV 2) (NV 0)))
>                                              , NV 0]))) 
>                                 ] :>: t)
>   canTy ev (Nu i o d x oi :>: Con t) = do
>     tv <- ev t
>     return $ Con (contTOp @@  [ i 
>                               , d $$ A o  
>                               , L (H (bwdList [i,o,d,x]) "t"
>                                    (N (casesOp :@ 
>                                        [ NV 4 , NV 3
>                                        , L (K SET) , NV 1  
>                                        , L ("oo" :. (NU (NV 5) (NV 4) 
>                                                      (NV 3) (NV 2) (NV 0)))
>                                        , NV 0])))
>                               ] :>: t)

> import -> OpCode where
>   boolE :: Tm {In,p} x
>   boolE = (CONSE (TAG "ff") (CONSE (TAG "tt") NILE))
>
>   boolT :: Tm {In,p} x
>   boolT = ENUMT boolE
>
>   sumTT :: EXTM
>   sumTT = 
>     L ("x" :. L ("y" :. 
>       SIGMA boolT 
>             (L ("b" :. (SIGMA (N (switchOp :@ [ boolE 
>                                               , NV 0
>                                               , L (K SET)
>                                               , PAIR (NV 2) (PAIR (NV 1) VOID) ]))
>                               (L (K UNIT)))))))
>     :? ARR SET (ARR SET SET)
>
>   sumVV :: VAL
>   sumVV = L (H B0 "x" (L ("y" :. N (sumTT :$ A (NV 1) :$ A (NV 2)))))  
>  
>   pattern LEFT x   = PAIR ZE (PAIR x VOID)  
>   pattern RIGHT y  = PAIR (SU ZE) (PAIR y VOID)  
>
>   casesOp :: Op
>   casesOp = Op
>     { opName = "cases" , opArity = 6 
>     , opTy = cOpTy , opRun = cOpRun 
>     } where
>       cOpTy ev [a , b , c , f , g , x] = Just $
>         ( [ SET :>: a , SET :>: b , ARR sumab SET :>: c
>           , PI va (L (H (B0 :< vc) "a" 
>                     (N (V 1 :$ A (LEFT (NV 0)))))) :>: f
>           , PI vb (L (H (B0 :< vc) "b" 
>                     (N (V 1 :$ A (RIGHT (NV 0)))))) :>: g
>           , sumab :>: x ]
>         , PI sumab (L (H (B0 :< vc) "ab" (N (V 1 :$ A (NV 0)))))) 
>        where va = ev a
>              vb = ev b
>              vc = ev c
>              sumab = sumVV $$ A va $$ A vb
>       cOpRun :: [VAL] -> Either NEU VAL
>       cOpRun [_ , _ , _ , f , _ , LEFT a ] = Right (f $$ A a)
>       cOpRun [_ , _ , _ , _ , g , RIGHT b ] = Right (g $$ A b)
>       cOpRun [_ , _ , _ , _ , _ , N x] = Left x
>   contTOp :: Op
>   contTOp = Op
>     { opName = "cont"
>     , opArity = 3
>     , opTy = cTOpTy
>     , opRun = cTOpRun
>     } where
>         cTOpTy ev [i , c , x] = 
>           Just ([ SET :>: i , CONTU vi :>: c , ARR vi SET :>: x ] , SET)
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
>          , ARR vi SET :>: x , ARR vi SET :>: y
>          , PI vi (L (H (B0 :< vx :< vy) "" 
>                     (ARR (N (V 2 :$ A (NV 0))) (N (V 1 :$ A (NV 0))))))
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
>               [ sumVV $$ A i $$ A o , c $$ A oi 
>               , L (H (bwdList [i , o , c , x]) "" 
>                   (N (casesOp :@ 
>                     [ NV 4 , NV 3 , L (K SET) , NV 1
>                     , L ("" :. N (contTOp :@ 
>                                    [ NV 5 , NV 3 , NV 0])) 
>                     , NV 0])))
>               , L (H (bwdList [i , o , c , y]) "" 
>                   (N (casesOp :@ 
>                     [ NV 4 , NV 3 , L (K SET) , NV 1
>                     , L ("" :. N (contTOp :@ 
>                                    [ NV 5 , NV 3 , NV 0])) 
>                     , NV 0])))
>               , L (H (bwdList [i , o , c , x , y , f]) "" 
>                   (N (casesOp :@ 
>                     [ NV 6
>                     , NV 5
>                     , (L ("" :. 
>                         (ARR (N (casesOp :@ 
>                                   [ NV 7 , NV 6 , L (K SET) , NV 4
>                                   , L ("" :. N (contTOp :@ 
>                                                  [ NV 8 , NV 6 , NV 0])) 
>                                   , NV 0])) 
>                              (N (casesOp :@ 
>                                   [ NV 7 , NV 6 , L (K SET) , NV 3
>                                   , L ("" :. N (contTOp :@ 
>                                                  [ NV 8 , NV 6 , NV 0])) 
>                                   , NV 0]))))) 
>                     , NV 1 
>                     , (L ("" :.  
>                         (L ("" :. 
>                           (N (mapCOp :@ [ NV 8  
>                                         , MUC (NV 7) (NV 6) (NV 1) 
>                                         , NV 5 , NV 4 , NV 3 
>                                         , NV 0 ]))))))
>                     , NV 0 ])))
>               , t ])  
>       mOpRun [i , NUC o c oi , x , y , f , t] = Right $ undefined
>       mOpRun [i , N c , x , y , f , t] = Left c 
>       mOpRun [i , c , x , y , f , N t] = Left t 
> 
>   
>   everyWhereOp :: Op
>   everyWhereOp = Op 
>     { opName = "Everywhere"
>     , opArity = 4
>     , opTy = eWOpTy
>     , opRun = eWOpRun
>     } where
>       eWOpTy ev [i , d , j , x , c , t] = Just $
>         ([ SET :>: i , CONTU vi :>: d , ARR vi SET :>: j 
>          , SET :>: x , ARR (SIGMA vi vj) (ev x) :>: c
>          , contTOp @@ [ vi , ev d , vj ] :>: t ] , CONTU (SIGMA vi vj))
>           where vi = ev i
>                 vj = ev j
>       eWOpTy _ _ = Nothing       
>       eWOpRun :: [VAL] -> Either NEU VAL
>       eWOpRun [i , REQC ii , j , x , c , jj] = Right $ 
>         REQC (c $$ A (PAIR ii jj))
>       eWOpRun [i , UNITC , j , x , c , t] = Right $ UNITC
>       eWOpRun [i , TIMESC a b , j , x , c , t] = Right $ TIMESC
>         (everyWhereOp @@ [i , a , j , x , c , t $$ Fst])
>         (everyWhereOp @@ [i , b , j , x , c , t $$ Snd])
>       eWOpRun [i , SIGMAC a b , j , x , c , t] = Right $ 
>         everyWhereOp @@ [i , b $$ A a , j , x , c , t $$ Snd]
>       eWOpRun [i , PIC a b , x , c , j , t] = Right $ PIC a 
>         (L (H (bwdList [i , b , j , x , c , t]) "" 
>               (N (everyWhereOp :@ [ NV 6 , N (V 5 :$ A (NV 0)) , NV 3 , NV 2
>                                  , NV 4 , N (V 1 :$ A (NV 0)) ]))))
>       eWOpRun [i , MUC o d oo , j , x , c , t] = Right $ MUC
>         (SIGMA o (L (H (bwdList [i , o , d , j]) "" 
>                    (MU (NV 4) (NV 3) (NV 2) (NV 1) (NV 0)))))
>         (L (H (bwdList [i , o , d , j , x , c]) "" (N
>           (everyWhereOp :@ 
>             [ NV 5 , N (V 2 :$ A (N (V 0 :$ Fst))) 
>             , L ("x'" :. N (casesOp :@ 
>                 [ NV 6 , NV 5 , L (K SET) , NV 2  
>                 , L ("oo" :. MU (NV 7) (NV 6) (NV 5) (NV 4) (NV 0)) , NV 0 ]))
>             , N (sumTT 
>                   :$ A (NV 2) 
>                   :$ A (SIGMA (NV 5) (L ("oo" :. MU (NV 7) (NV 6) 
>                                                     (NV 5) (NV 4) (NV 0)))))
>             , L ("x" :. N (splitOp :@ 
>                   [ N (sumTT :$ A (NV 7) :$ A (NV 6))
>                   , L ("io" :. N (casesOp :@ 
>                         [ NV 8 , NV 7 , L (K SET) , NV 5 
>                         , L ("oo" :. MU (NV 8) (NV 7) (NV 6) (NV 5) (NV 0))
>                         , NV 0]))
>                   , NV 0 
>                   , L (K (N (sumTT 
>                               :$ A (NV 3) 
>                               :$ A (SIGMA (NV 6) 
>                                    (L ("oo" :. MU (NV 9) (NV 8) 
>                                                   (NV 7) (NV 6) (NV 0)))))))
>                   , L ("io" :. N (casesOp :@ 
>                         [ NV 8 , NV 7 
>                         , L ("oo" :. ARR 
>                                 (N (casesOp :@ 
>                                   [ NV 9 , NV 8 , L (K SET) , NV 6 
>                                   , L ("oo" :. MU (NV 9) (NV 8) 
>                                                   (NV 7) (NV 6) (NV 0))
>                                   , NV 0 ])) 
>                                 (N (sumTT 
>                                      :$ A (NV 3)  
>                                      :$ A (SIGMA (NV 6) (L ("oo" :. 
>                                                MU (NV 9) (NV 8) 
>                                                   (NV 7) (NV 6) (NV 0)))))))
>                         , L ("i" :. L ("j" :. 
>                             LEFT (N (V 5 :$ A (PAIR (NV 1) (NV 0))))))
>                         , L ("o''" :. L ("t''" :. 
>                             RIGHT (PAIR (NV 1) (NV 0))))
>                         , NV 0])) ])) 
>             , N (V 0 :$ Snd :$ Out) ]))))
>         (PAIR oo t)
>       eWOpRun [i , N d , j , x , c , t] = Left d
>       eWOpRun [i , d , j , x , c , N t] = Left t


> import -> Operators where
>   casesOp :
>   contTOp : 
>   mapCOp :


> -- import -> ElimTyRules where

> -- import -> EtaExpand where
