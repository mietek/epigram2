\section{IDesc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.IDesc where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where
>   IMu     :: Labelled (Id :*: Id) t -> t -> Can t

> import -> CanTyRules where
>   canTy chev (Set :>: IMu (ml :?=: (Id ii :& Id x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (idesc $$ A iiv $$ A VOID) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ IMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
>   canTy chev (IMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>     yyv <- chev (idescOp @@ [ ii
>                             , x $$ A i 
>                             , L $ HF "i" $ \i -> C (IMu tt i)
>                             ] :>: y)
>     return $ Con yyv

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where
>   pattern IVARN     = ZE
>   pattern ICONSTN   = SU ZE
>   pattern IPIN      = SU (SU ZE)
>   pattern IFPIN     = SU (SU (SU ZE))
>   pattern ISIGMAN   = SU (SU (SU (SU ZE)))
>   pattern IFSIGMAN  = SU (SU (SU (SU (SU ZE))))
>   pattern IPRODN    = SU (SU (SU (SU (SU (SU ZE)))))

>   pattern IMU l ii x i  = C (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern IVAR i        = CON (PAIR IVARN     (PAIR i VOID))
>   pattern IPI s t       = CON (PAIR IPIN      (PAIR s (PAIR t VOID)))
>   pattern IFPI s t      = CON (PAIR IFPIN     (PAIR s (PAIR t VOID)))
>   pattern ISIGMA s t    = CON (PAIR ISIGMAN   (PAIR s (PAIR t VOID)))
>   pattern IFSIGMA s t   = CON (PAIR IFSIGMAN  (PAIR s (PAIR t VOID)))
>   pattern ICONST p      = CON (PAIR ICONSTN   (PAIR p VOID))
>   pattern IPROD x y     = CON (PAIR IPRODN    (PAIR x (PAIR y VOID)))

> import -> CanDisplayPats where
>   pattern DIVARN     = DZE
>   pattern DICONSTN   = DSU DZE
>   pattern DIPIN      = DSU (DSU DZE)
>   pattern DIFPIN     = DSU (DSU (DSU DZE))
>   pattern DISIGMAN   = DSU (DSU (DSU (DSU DZE)))
>   pattern DIFSIGMAN  = DSU (DSU (DSU (DSU (DSU DZE))))
>   pattern DIPRODN    = DSU (DSU (DSU (DSU (DSU (DSU DZE)))))

>   pattern DIMU l ii x i  = DC (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern DIVAR i        = DCON (DPAIR DIVARN     (DPAIR i DVOID))
>   pattern DIPI s t       = DCON (DPAIR DIPIN      (DPAIR s (DPAIR t DVOID)))
>   pattern DIFPI s t      = DCON (DPAIR DIFPIN     (DPAIR s (DPAIR t DVOID)))
>   pattern DISIGMA s t    = DCON (DPAIR DISIGMAN   (DPAIR s (DPAIR t DVOID)))
>   pattern DIFSIGMA s t   = DCON (DPAIR DIFSIGMAN  (DPAIR s (DPAIR t DVOID)))
>   pattern DICONST p      = DCON (DPAIR DICONSTN   (DPAIR p DVOID))
>   pattern DIPROD x y     = DCON (DPAIR DIPRODN    (DPAIR x (DPAIR y DVOID)))


> import -> CanPretty where
>   pretty (IMu (Just l   :?=: _) i)  = wrapDoc
>       (pretty l AppSize <+> pretty i ArgSize)
>       AppSize
>   pretty (IMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>       (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>       AppSize

> import -> CanTraverse where
>   traverse f (IMu l i)     = (|IMu (traverse f l) (f i)|)

> import -> CanHalfZip where
>   halfZip (IMu l0 i0) (IMu l1 i1) = (|(\p -> IMu p (i0,i1)) (halfZip l0 l1)|)

> import -> Coerce where
>   -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
>   coerce (IMu (Just (l0,l1) :?=: 
>               (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) = 
>     let ql  = CON $ q $$ Fst
>         qiI = CON $ q $$ Snd $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Snd $$ Fst
>         (typ :>: vap) = 
>           laty ("I" :<: SET :-: \iI ->
>                 "d" :<: ARR iI (idesc $$ A iI $$ A VOID) :-: \d ->
>                 "i" :<: iI :-: \i ->
>                 "l" :<: ARR iI SET :-: \l ->
>                 Target (SET :>: 
>                           idescOp @@ [ iI , d $$ A i
>                                      , L $ HF "i" $ IMU (|l|) iI d
>                                      ]))
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [iI0, d0 $$ A i0, L $ HF "i" $ IMU (|l0|) iI0 d0] 
>              , idescOp @@ [iI1, d1 $$ A i1, L $ HF "i" $ IMU (|l1|) iI1 d1] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>                                $$ A l0 $$ A l1 $$ A ql
>              , x ]
>   coerce (IMu (Nothing :?=: (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>     let qiI = CON $ q $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Fst
>         (typ :>: vap) = 
>           laty ("I" :<: SET :-: \iI ->
>                 "d" :<: ARR iI (idesc $$ A iI $$ A VOID) :-: \d ->
>                 "i" :<: iI :-: \i ->
>                 Target (SET :>: 
>                           (idescOp @@ [ iI , d $$ A i
>                                       , L $ HF "i" $ IMU Nothing iI d
>                                       ]))) 
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0 , L $ HF "i" $ IMU Nothing iI0 d0 ] 
>              , idescOp @@ [ iI1 , d1 $$ A i1 , L $ HF "i" $ IMU Nothing iI1 d1 ] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>              , x ]


\subsection{Plugging Eliminators in}

> import -> ElimTyRules where
>   elimTy chev (_ :<: (IMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>     return (Out, idescOp @@ [ii , x $$ A i , L $ HF "i" $ \i -> C (IMu tt i)])

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

\subsection{Plugging Operators in}

> import -> Operators where
>   idescOp :
>   iboxOp :
>   imapBoxOp :
>   iinductionOp :

> import -> OpCompile where

%if False

<  ("iinduction", [iI,d,i,v,bp,p]) -> App (Var "__iinduction") [d, p, i, v]
<  ("imapBox", [iI,d,x,bp,p,v]) -> App (Var "__imapBox") [d, p, v]

%endif

> import -> OpCode where
>   type IDescDispatchTable = (VAL -> VAL,
>                              VAL -> VAL -> VAL,
>                              VAL -> VAL -> VAL,
>                              VAL -> VAL -> VAL,
>                              VAL -> VAL -> VAL,
>                              VAL -> VAL,
>                              VAL -> VAL -> VAL)

>   mkLazyIDescDef :: VAL -> IDescDispatchTable -> Either NEU VAL
>   mkLazyIDescDef arg (ivarC, ipiC, ifpiC, isigmaC, ifsigmaC, iconstC, iprodC) =
>     let args = arg $$ Snd in
>       case arg $$ Fst of      
>         IVARN     -> Right $ ivarC (args $$ Fst)
>         IPIN      -> Right $ ipiC (args $$ Fst) (args $$ Snd $$ Fst) 
>         IFPIN     -> Right $ ifpiC (args $$ Fst)  (args $$ Snd $$ Fst)
>         ISIGMAN   -> Right $ isigmaC (args $$ Fst) (args $$ Snd $$ Fst)
>         IFSIGMAN  -> Right $ ifsigmaC (args $$ Fst) (args $$ Snd $$ Fst)
>         ICONSTN   -> Right $ iconstC (args $$ Fst) 
>         IPRODN    -> Right $ iprodC (args $$ Fst) (args $$ Snd $$ Fst)
>         N t     -> Left t

>   idescOp :: Op
>   idescOp = Op
>     { opName = "idesc"
>     , opArity = 3
>     , opTyTel = idOpTy
>     , opRun = idOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       idOpTy = 
>        "I" :<: SET :-: \iI ->
>        "d" :<: (idesc $$ A iI $$ A VOID) :-: \d ->
>        "X" :<: ARR iI SET :-: \x ->
>        Target SET
>       idOpRun :: [VAL] -> Either NEU VAL
>       idOpRun [_I, CON _D, _P] = 
>         mkLazyIDescDef _D  (  ivarD _I _P
>                            ,  ipiD _I _P        
>                            ,  ifpiD _I _P        
>                            ,  isigmaD _I _P        
>                            ,  ifsigmaD _I _P        
>                            ,  iconstD _I _P        
>                            ,  iprodD _I _P  
>                            )
>       idOpRun [_I, N n, _P] = Left n 
>       idOpRun x = error (show . length $ x)
>       ivarD _I _P i = _P $$ A i     
>       ipiD _I _P _S _T =
>           PI _S (L . HF "s" $ \s ->
>                  idescOp @@ [ _I, _T $$ A s, _P ])
>       ifpiD _I _P _E _Df =
>           branchesOp @@  [  _E
>                          ,  (L . HF "e" $ \e -> 
>                                idescOp @@  [  _I,  _Df $$ A e,  _P ]) 
>                          ]
>       isigmaD _I _P _S _T = 
>           SIGMA _S (L . HF "s" $ \s ->
>                     idescOp @@ [  _I
>                                ,  _T $$ A s
>                                ,  _P ])
>       ifsigmaD _I _P _E _Ds =
>           SIGMA (ENUMT _E) (L . HF "s" $ \s ->
>                             idescOp @@ [ _I
>                                        , switchOp @@ [ _E
>                                                      , s
>                                                      , LK (idesc $$ A _I $$ A VOID)
>                                                      , _Ds]
>                                        , _P])
>       iconstD _I _P _K = _K
>       iprodD _I _P _D _D' =
>           TIMES  (idescOp @@ [ _I, _D, _P ])
>                  (idescOp @@ [ _I, _D', _P ])

>   iboxOp :: Op
>   iboxOp = Op
>     { opName = "ibox"
>     , opArity = 4
>     , opTyTel = iboxOpTy
>     , opRun = iboxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       iboxOpTy = 
>         "I" :<: SET                        :-: \ _I ->
>         "D" :<: (idesc $$ A _I $$ A VOID)  :-: \ _D ->
>         "P" :<: ARR _I SET                 :-: \ _P ->
>         "v" :<: idescOp @@ [_I,_D,_P]      :-: \v ->
>         Target $ idesc $$ A (SIGMA _I (L . HF "i" $ \i -> _P $$ A i)) $$ A VOID
>       iboxOpRun :: [VAL] -> Either NEU VAL
>       iboxOpRun [_I,CON _D,_P,v] = 
>         mkLazyIDescDef _D  (  ivarD _I _P v
>                            ,  ipiD _I _P v       
>                            ,  ifpiD _I _P v       
>                            ,  isigmaD _I _P v        
>                            ,  ifsigmaD _I _P v       
>                            ,  iconstD _I _P v       
>                            ,  iprodD _I _P v 
>                            )
>       iboxOpRun [_I,N _D,_P,v] = Left _D
>       ivarD _I _P v i = IVAR (PAIR i v)
>       ipiD _I _P f _S _T =
>           IPI _S (L . HF "s" $ \s ->
>                    iboxOp @@ [_I, _T $$ A s, _P, f $$ A s])
>       ifpiD _I _P t _E _Df =
>           IFPI _E (L . HF "e" $ \e ->
>                     iboxOp @@  [  _I, _Df $$ A e, _P
>                                ,  switchOp @@ [_E, e, 
>                                     L (HF "e" $ \e -> 
>                                       idescOp @@ [_I, _Df $$ A e,_P]), t]])
>       isigmaD _I _P sd _S _T =
>           let s = sd $$ Fst
>               d = sd $$ Snd in
>           iboxOp @@ [_I, _T $$ A s, _P, d]
>       ifsigmaD _I _P ed _S _T =
>            let e = ed $$ Fst
>                d = ed $$ Snd in
>            iboxOp @@ [_I
>                      , switchOp @@ [ _S
>                                    , e
>                                    , LK (idesc $$ A _I $$ A VOID)
>                                    , _T ]
>                      , _P 
>                      , d ]
>       iconstD _I _P _ _K = ICONST (PRF TRIVIAL)
>       iprodD _I _P dd' _D _D' =
>           let d = dd' $$ Fst
>               d' = dd' $$ Snd in
>           IPROD  (iboxOp @@ [_I, _D, _P, d])
>                   (iboxOp @@ [_I, _D', _P, d'])
          
>   imapBoxOp :: Op
>   imapBoxOp = Op
>     { opName = "imapBox"
>     , opArity = 6
>     , opTyTel = imapBoxOpTy
>     , opRun = imapBoxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       imapBoxOpTy =
>         "I" :<: SET :-: \_I ->  
>         "D" :<: (idesc $$ A _I $$ A VOID) :-: \ _D ->
>         "X" :<: ARR _I SET :-: \ _X -> 
>         let _IX = SIGMA _I (L . HF "i" $ \i -> _X $$ A i) in
>         "P" :<: ARR _IX SET :-: \ _P ->
>         "p" :<: (pity $ "ix" :<: _IX :-: \ ix -> Target $ _P $$ A ix) :-: \ _ ->
>         "v" :<: (idescOp @@ [_I,_D,_X]) :-: \v ->
>          Target (idescOp @@ [_IX, iboxOp @@ [_I,_D,_X,v], _P])
>       imapBoxOpRun :: [VAL] -> Either NEU VAL
>       imapBoxOpRun [_I, CON _D, _X, _P, p, v]  = 
>         mkLazyIDescDef _D (varD _I _X _P p v, 
>                            piD _I _X _P p v,
>                            fpiD _I _X _P p v,
>                            sigmaD _I _X _P p v,
>                            fsigmaD _I _X _P p v,
>                            constD _I _X _P p v, 
>                            prodD _I _X _P p v) 
>       imapBoxOpRun [_I, N _D, _X, _P, p, v]  = Left _D
>       varD _I _X _P p v i = p $$ A (PAIR i v)
>       piD _I _X _P p v _S _T = 
>         L . HF "s" $ \s -> imapBoxOp @@ [_I,_T $$ A s,_X,_P,p,v $$ A s]
>       fpiD _I _X _P p v _E _Df = 
>         L . HF "s" $ \s -> imapBoxOp @@ [_I,_Df $$ A s,_X,_P,p,v $$ A s]
>       sigmaD _I _X _P p v _S _T = imapBoxOp @@ [_I,_T $$ A (v $$ Fst),_X,_P,p,v $$ Snd]
>       fsigmaD _I _X _P p v _E _Ds =
>         imapBoxOp @@ [_I,switchOp @@ [_E,v $$ Fst,LK (idesc $$ A _I $$ A VOID),_Ds],_X,_P,p,v $$ Snd]
>       constD _I _X _P p v _K = VOID
>       prodD _I _X _P p v _D _D' = 
>         PAIR (imapBoxOp @@ [_I,_D,_X,_P,p,v $$ Fst]) 
>               (imapBoxOp @@ [_I,_D',_X,_P,p,v $$ Snd])

>   iinductionOpMethodType = L . HF "I" $ \_I -> 
>                      L . HF "D" $ \_D ->
>                      L . HF "P" $ \_P -> pity $ 
>                        "i" :<: _I :-: \i ->
>                        let mud = L . HF "i" $ \i -> IMU Nothing _I _D i in
>                        "x" :<: (idescOp @@ [ _I, _D $$ A i, mud])
>                                  :-: \x -> Target $
>                          ARR (idescOp @@ [ SIGMA _I mud
>                                         , iboxOp @@ [_I, _D $$ A i, mud, x], _P ])
>                              (_P $$ A (PAIR i (CON x)))

<   iinductionOpLabMethodType = L . HF "l" $ \l ->
<                         L . HF "d" $ \d ->
<                         L . HF "P" $ \_P ->
<                         PI (descOp @@ [d, MU (Just l) d])
<                            (L . HF "x" $ \x ->
<                             ARR (boxOp @@ [d, MU (Just l) d, _P, x])
<                                 (_P $$ A (PAIR CON x)))

>   iinductionOp :: Op
>   iinductionOp = Op
>     { opName = "iinduction"
>     , opArity = 6
>     , opTyTel = iinductionOpTy
>     , opRun = iinductionOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       iinductionOpTy = 
>         "I" :<: SET :-: \_I ->
>         "D" :<: ARR _I (idesc $$ A _I $$ A VOID) :-: \_D ->
>         "i" :<: _I :-: \i ->
>         "v" :<: IMU Nothing _I _D i :-: \v ->
>         "P" :<: (ARR (SIGMA _I (L . HF "i" $ \i -> IMU Nothing _I _D i)) SET) :-: \_P ->
>         "p" :<: (iinductionOpMethodType $$ A _I $$ A _D $$ A _P) :-: \p ->
>         Target (_P $$ A (PAIR i v))
>       iinductionOpRun :: [VAL] -> Either NEU VAL
>       iinductionOpRun [_I, _D, i, CON v, _P, p] = Right $ 
>        p $$ A i $$ A v 
>          $$ A (imapBoxOp @@ [ _I, _D $$ A i 
>                             , (L . HF "i" $ \i -> IMU Nothing _I _D i), _P
>                             , L . HF "ix" $ \ix -> 
>                                iinductionOp @@ 
>                                  [ _I, _D, ix $$ Fst, ix $$ Snd, _P, p ]
>                             , v]) 
>       iinductionOpRun [_, _, _, N x, _,_] = Left x

> import -> KeywordConstructors where
>   KwIMu :: Keyword

> import -> KeywordTable where
>   key KwIMu      = "IMu"

> import -> DInTmParsersSpecial where
>   (AndSize, (|(DIMU Nothing) (%keyword KwIMu%) (sizedDInTm ArgSize) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :


Just like |Mu|, when elaborating |IMu| we attach a display label if the
description is not neutral, to improve the pretty-printed representation.

> import -> MakeElabRules where
>   makeElab' loc (SET :>: DIMU Nothing iI d i) = do
>       (r,sp) <- eFake
>       let l = (P r) $:$ (init sp)
>       iI  :=>: iIv  <- subElab loc (SET :>: iI)
>       d   :=>: dv   <- subElab loc (ARR iIv (idesc $$ A iIv $$ A VOID) :>: d)
>       i   :=>: iv   <- subElab loc (iIv :>: i)

\question{What is this check for? How can we implement it correctly?}

<       guard =<< eEqual (SET :>: (iv, NP (last sp)))
<       -- should check i doesn't appear in d (fairly safe it's not in iI :))

>       if shouldLabel dv
>           then return $ IMU (Just (N l)) iI d i
>                             :=>: IMU (Just (evTm l)) iIv dv iv
>           else return $ IMU Nothing iI d i
>                             :=>: IMU Nothing iIv dv iv
>    where
>      shouldLabel :: VAL -> Bool
>      shouldLabel (N _)  = False
>      shouldLabel _      = True


>   makeElab' loc (ty@(IMU _ _ _ _) :>: DTag s xs) =
>       makeElab' loc (ty :>: DCON (DPAIR (DTAG s) (foldr DPAIR DU xs)))

> import -> DistillRules where

>     distill es (IMU l _I s i :>: CON (PAIR t x)) 
>       | Just (e, f) <- sumilike _I (s $$ A i) = do
>         m   :=>: tv  <- distill es (ENUMT e :>: t)
>         as  :=>: xv  <- distill es (idescOp @@ [  _I,f tv
>                                                ,  L (HF "i" $ \i -> IMU l _I s i)
>                                                ] :>: x)
>         case m of
>             DTAG s   -> return $ DTag s (unfold as)  :=>: CON (PAIR tv xv)
>             _        -> return $ DCON (DPAIR m as)   :=>: CON (PAIR tv xv)
>       where
>         unfold :: DInTmRN -> [DInTmRN]
>         unfold DVOID        = []
>         unfold DU        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]
>         sumilike :: VAL -> VAL -> Maybe (VAL, VAL -> VAL)
>         sumilike _I (IFSIGMA e b)  = 
>           Just (e, \t -> switchOp @@ [ e , t , LK (idesc $$ A _I $$ A VOID), b ])
>         sumilike _ _               = Nothing

> import -> DInTmConstructors where

> import -> DInTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
>   ("IDesc", idescREF) :
>   ("IDescD", idescDREF) :


> import -> RulesCode where
>   inIDesc :: VAL
>   inIDesc = L $ HF "I" $ \_I -> LK $ IFSIGMA constructors (cases _I)
>       where constructors = (CONSE (TAG "varD")
>                            (CONSE (TAG "constD")
>                            (CONSE (TAG "piD")
>                            (CONSE (TAG "fpiD")
>                            (CONSE (TAG "sigmaD")
>                            (CONSE (TAG "fsigmaD")
>                            (CONSE (TAG "prodD")
>                             NILE)))))))
>             cases _I = (PAIR (ISIGMA _I (LK $ ICONST UNIT)) 
>                     (PAIR (ISIGMA SET (LK $ ICONST UNIT))
>                     (PAIR (ISIGMA SET (L $ HF "S" $ \_S -> 
>                                       (IPROD (IPI _S (LK $ IVAR VOID)) 
>                                              (ICONST UNIT))))
>                     (PAIR (ISIGMA enumU (L $ HF "E" $ \_E ->
>                                       (IPROD (IPI (ENUMT _E) (LK $ IVAR VOID))
>                                              (ICONST UNIT))))
>                     (PAIR (ISIGMA SET (L $ HF "S" $ \_S -> 
>                                       (IPROD (IPI _S (LK $ IVAR VOID)) 
>                                              (ICONST UNIT))))
>                     (PAIR (ISIGMA enumU (L $ HF "E" $ \_E ->
>                                       (IPROD (IFPI _E (LK $ IVAR VOID))
>                                              (ICONST UNIT))))
>                     (PAIR (IPROD (IVAR VOID) (IPROD (IVAR VOID) (ICONST UNIT)))
>                      VOID)))))))
>   idescFakeREF :: REF
>   idescFakeREF = [("Primitive", 0), ("IDesc", 0)] 
>                    := (FAKE :<: ARR SET (ARR UNIT SET))
>   idesc :: VAL
>   idesc = L $ HF "I" $ \_I -> LK $
>             IMU (Just ((N (P idescFakeREF)) $$ A _I)) UNIT (inIDesc $$ A _I) VOID
>
>   idescREF :: REF
>   idescREF = [("Primitive", 0), ("IDesc", 0)] 
>                := (DEFN idesc :<: ARR SET (ARR UNIT SET))
>
>   idescDREF :: REF
>   idescDREF = [("Primitive", 0), ("IDescD", 0)] 
>                 := (DEFN inIDesc 
>                      :<: PI SET (L $ HF "I" $ \_I -> 
>                             ARR UNIT (idesc $$ A _I $$ A VOID)))

