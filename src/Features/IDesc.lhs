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

>   idescOp :: Op
>   idescOp = Op
>     { opName = "idesc"
>     , opArity = 3
>     , opTyTel = idOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData {- idOpRun -}
>         [ {-VAR-} oTup $ \i -> OLam $ \_P -> ORet $ _P $$ A i
>         , {-CONST-} oTup $ \_A -> OLam $ \_P -> ORet _A
>         , {-PI-} oTup $ \_S _T -> OLam $ \_P -> ORet $
>                    PI _S $ L $ "s" :. [.s. N $ 
>                      idescOp :@ [ _I -$ [] , _T -$ [NV s], _P -$ [] ]]   
>         , {-FPI-} oTup $ \_E _Df -> OLam $ \_P -> ORet $ 
>                     branchesOp @@  
>                       [  _E 
>                       ,  (L $ "e" :. [.e. N $  
>                             idescOp :@  [  _I -$ []
>                                         ,  _Df -$ [NV e]
>                                         ,  _P -$ [] 
>                                         ]]) 
>                       ]
>         , {-SIGMA-} oTup $ \_S _T -> OLam $ \_P -> ORet $
>                       SIGMA _S $ L $ "s" :. [.s. N $ 
>                         idescOp :@ [ _I -$ [] , _T -$ [NV s], _P -$ [] ]]  
>         , {-FSIGMA-} oTup $ \_E _Ds -> OLam $ \_P -> ORet $
>                        SIGMA (ENUMT _E) (L $ "s" :. [.s. N $
>                          idescOp :@ [ _I -$ []
>                                     , N $ switchOp :@ 
>                                             [ _E -$ []
>                                             , NV s
>                                             , LK (idesc -$ [ _I -$ []
>                                                            ,  VOID])
>                                             , _Ds -$ [] ]
>                                     , _P -$ [] ] ])
>         , {-PROD-} oTup $ \_D _D' -> OLam $ \_P -> ORet $
>                      TIMES (idescOp @@ [_I, _D, _P]) (idescOp @@ [_I, _D', _P])
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       idOpTy = 
>        "I" :<: SET :-: \iI ->
>        "d" :<: (idesc $$ A iI $$ A VOID) :-: \d ->
>        "X" :<: ARR iI SET :-: \x ->
>        Target SET

>   iboxOp :: Op
>   iboxOp = Op
>     { opName = "ibox"
>     , opArity = 4
>     , opTyTel = iboxOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData  {- iboxOpRun -}
>         [ {-VAR-} oTup $ \i -> oLams $ \() v -> ORet $ 
>                     IVAR (PAIR i v)
>         , {-CONST-} oTup $ \() -> oLams $ \() () -> ORet $
>                        ICONST (PRF TRIVIAL)
>         , {-PI-} oTup $ \_S _T -> oLams $ \_P f -> ORet $
>                    IPI _S (L $ "s" :. [.s. N $
>                      iboxOp :@  [  _I -$ [], _T -$ [NV s]
>                                 ,  _P -$ [], f -$ [NV s]] ])
>         , {-FPI-} oTup $ \_E _Df -> oLams $ \_P v -> ORet $ 
>                     IFPI _E (L $ "e" :. [.e. N $ 
>                       iboxOp :@  [  _I -$ [] , _Df -$ [NV e], _P -$ []
>                                  ,  N $ switchOp :@ 
>                                           [  _E -$ [] , NV e  
>                                           ,  L $ "f" :. [.f. N $  
>                                                idescOp :@  [  _I -$ []
>                                                            ,  _Df -$ [NV f]
>                                                            , _P -$ [] ] ]
>                                           ,  v -$ []]]])
>         , {-SIGMA-} oTup $ \() _T -> OLam $ \_P -> OPr $ oLams $ \s d -> ORet $
>                       iboxOp @@ [_I, _T $$ A s, _P, d]
>         , {-FSIGMA-} oTup $ \_E _Ds -> OLam $ \_P -> OPr $ oLams $ \e d -> ORet $
>             iboxOp @@ [_I
>                       , switchOp @@ [ _E
>                                     , e
>                                     , LK (idesc $$ A _I $$ A VOID)
>                                     , _Ds ]
>                       , _P 
>                       , d ]
>         , {-PROD-} oTup $ \_D _D' -> OLam $ \_P -> OPr $ oLams $ \d d' -> ORet $
>             IPROD  (iboxOp @@ [_I, _D, _P, d])
>                     (iboxOp @@ [_I, _D', _P, d'])
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       iboxOpTy = 
>         "I" :<: SET                        :-: \ _I ->
>         "D" :<: (idesc $$ A _I $$ A VOID)  :-: \ _D ->
>         "P" :<: ARR _I SET                 :-: \ _P ->
>         "v" :<: idescOp @@ [_I,_D,_P]      :-: \v ->
>         Target $ idesc $$ A (SIGMA _I (L . HF "i" $ \i -> _P $$ A i)) $$ A VOID
          
>   imapBoxOp :: Op
>   imapBoxOp = Op
>     { opName = "imapBox"
>     , opArity = 6
>     , opTyTel = imapBoxOpTy
>     , opRun = runOpTree $ OLam $ \_I -> oData {- imapBoxOpRun -}
>         [ {-VAR-} oTup $ \i -> oLams $ \() () p v -> ORet $ p $$ A (PAIR i v)
>         , {-CONST-} oTup $ \() -> oLams $ \() () () () -> ORet $ VOID
>         , {-PI-} oTup $ \() _T -> oLams $ \_X _P p f -> ORet $
>             L $ "s" :. [.s. N $ 
>               imapBoxOp :@  [  _I -$ [], _T -$ [NV s]
>                             ,  _X -$ [] ,_P -$ [], p -$ [], f -$ [NV s] ] ]
>         , {-FPI-} oTup $ \() _Df -> oLams $ \_X _P p v -> ORet $ 
>             L $ "s" :. [.s. N $ 
>               imapBoxOp :@  [  _I -$ [], _Df -$ [NV s]
>                             ,  _X -$ [] ,_P -$ [], p -$ [], v -$ [NV s] ] ]
>         , {-SIGMA-} oTup $ \() _T -> oLams $ \_X _P p -> OPr $ oLams $ \s d -> ORet $
>             imapBoxOp @@ [  _I, _T $$ A s, _X, _P, p, d]
>         , {-FSIGMA-} oTup $ \_E _Ds -> oLams $ \_X _P p -> OPr $ oLams $ \e d -> ORet $
>             imapBoxOp @@ [  _I
>                          ,  switchOp @@ [  _E, e 
>                                         ,  LK (idesc $$ A _I $$ A VOID)
>                                         ,  _Ds
>                                         ]
>                          ,  _X, _P, p, d ]
>         , {-PROD-} oTup $ \_D _D' -> oLams $ \_X _P p -> OPr $ oLams $ \d d' -> ORet $
>             PAIR (imapBoxOp @@ [_I, _D, _X, _P, p, d]) 
>                   (imapBoxOp @@ [_I, _D', _X, _P, p, d'])
>         ]
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
>     , opRun = runOpTree $ oLams $ \_I _D i -> OCon $ oLams $ \v _P p -> ORet $
>         p $$ A i $$ A v 
>           $$ A (imapBoxOp @@ [ _I, _D $$ A i 
>                              , (L $ "i" :. [.i.   
>                                  IMU Nothing (_I -$ []) (_D -$ []) (NV i)])
>                              , _P
>                              , L $ "ix" :. [.ix. N $  
>                                 iinductionOp :@ 
>                                   [ _I -$ [], _D -$ []
>                                   , N (V ix :$ Fst), N (V ix :$ Snd)
>                                   , _P -$ [], p -$ [] ] ]
>                              , v]) 
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
>                      :<: ARR SET (ARR UNIT (idesc $$ A UNIT $$ A VOID)))

