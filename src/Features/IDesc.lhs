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
>                             , L $ "i" :. [.i. 
>                                 C (IMu (fmap (-$ []) tt) (NV i)) ]
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
>                                      , L $ "i" :. [.i. 
>                                          IMU (|(l -$ [])|) (iI -$ []) (d -$ []) (NV i)]
>                                      ]))
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [  iI0, d0 $$ A i0 
>                           ,  L $ "i" :. [.i. 
>                               IMU (|(l0 -$ [])|) (iI0 -$ []) (d0 -$ []) (NV i)
>                              ] 
>                           ] 
>              , idescOp @@ [  iI1, d1 $$ A i1 
>                           ,  L $ "i" :. [.i. 
>                               IMU (|(l1 -$ [])|) (iI1 -$ []) (d1 -$ []) (NV i)
>                              ]
>                           ] 
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
>                 Target 
>                  (SET :>: 
>                    (idescOp @@ [ iI , d $$ A i
>                                , L $ "i" :. [.i.
>                                    IMU Nothing (iI -$ []) (d -$ []) (NV i)]
>                                ]))) 
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0
>                           , L $ "i" :. [.i. 
>                               IMU Nothing (iI0 -$ []) (d0 -$ []) (NV i) ] ] 
>              , idescOp @@ [ iI1 , d1 $$ A i1
>                           , L $ "i" :. [.i. 
>                               IMU Nothing (iI1 -$ []) (d1 -$ []) (NV i) ] ] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>              , x ]


\subsection{Plugging Eliminators in}

> import -> ElimTyRules where
>   elimTy chev (_ :<: (IMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>     return (Out, 
>       idescOp @@ [  ii , x $$ A i 
>                  ,  L $ "i" :. [.i. C (IMu (fmap (-$ []) tt) (NV i)) ] ])

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
>         Target $ idesc $$ A (SIGMA _I (L $ "i" :. [.i. _P -$ [NV i]])) $$ A VOID
          
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
>         let _IX = SIGMA _I (L $ "i" :. [.i. _X -$ [NV i] ]) in
>         "P" :<: ARR _IX SET :-: \ _P ->
>         "p" :<: (pity $ "ix" :<: _IX :-: \ ix -> Target $ _P $$ A ix) :-: \ _ ->
>         "v" :<: (idescOp @@ [_I,_D,_X]) :-: \v ->
>          Target (idescOp @@ [_IX, iboxOp @@ [_I,_D,_X,v], _P])

>   iinductionOpMethodType _I _D _P = pity $ 
>                        "i" :<: _I :-: \i ->
>                        let mud = L $ "i" :. [.i. IMU Nothing (_I -$ []) (_D -$ []) (NV i) ] in
>                        "x" :<: (idescOp @@ [ _I, _D $$ A i, mud])
>                                  :-: \x -> Target $
>                          ARR (idescOp @@ [ SIGMA _I mud
>                                         , iboxOp @@ [_I, _D $$ A i, mud, x], _P ])
>                              (_P $$ A (PAIR i (CON x))) 

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
>         "P" :<: (ARR (SIGMA _I (L $ "i" :. [.i.  
>                   IMU Nothing (_I -$ []) (_D -$ []) (NV i) ])) SET) :-: \_P ->
>         "p" :<: (iinductionOpMethodType _I _D _P) :-: \p ->
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
>         as  :=>: xv  <- 
>           distill es (idescOp @@ [  _I,f tv
>                                  ,  L $ "i" :. [.i. 
>                                       IMU (fmap (-$ []) l) 
>                                           (_I -$ []) (s -$ []) (NV i)]
>                                  ] :>: x)
>         case m of
>             DTAG s   -> return $ DTag s (unfold as)  :=>: CON (PAIR tv xv)
>             _        -> return $ DCON (DPAIR m as)   :=>: CON (PAIR tv xv)
>       where
>         unfold :: DInTmRN -> [DInTmRN]
>         unfold DVOID        = []
>         unfold DU        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]


> import -> DInTmConstructors where

> import -> DInTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
>   ("IDesc", idescREF) :
>   ("IDescD", idescDREF) :
>   ("icase", icaseREF) :
>   ("idind", idindREF) :


> import -> RulesCode where
>   inIDesc :: VAL
>   inIDesc = L $ "I" :. [._I. LK $ IFSIGMA constructors (cases (NV _I)) ]
>       where constructors = (CONSE (TAG "varD")
>                            (CONSE (TAG "constD")
>                            (CONSE (TAG "piD")
>                            (CONSE (TAG "fpiD")
>                            (CONSE (TAG "sigmaD")
>                            (CONSE (TAG "fsigmaD")
>                            (CONSE (TAG "prodD") 
>                             NILE)))))))
>             cases :: INTM -> INTM
>             cases _I = (PAIR (ISIGMA _I (LK $ ICONST UNIT)) 
>                     (PAIR (ISIGMA SET (LK $ ICONST UNIT))
>                     (PAIR (ISIGMA SET (L $ "S" :. [._S.  
>                                       (IPROD (IPI (NV _S) (LK $ IVAR VOID)) 
>                                              (ICONST UNIT))]))
>                     (PAIR (ISIGMA (enumU -$ []) (L $ "E" :. [._E.
>                                       (IPROD (IPI (ENUMT (NV _E)) (LK $ IVAR VOID))
>                                              (ICONST UNIT))]))
>                     (PAIR (ISIGMA SET (L $ "S" :. [._S.  
>                                       (IPROD (IPI (NV _S) (LK $ IVAR VOID)) 
>                                              (ICONST UNIT))]))
>                     (PAIR (ISIGMA (enumU -$ []) (L $ "E" :. [._E.
>                                       (IPROD (IFPI (NV _E) (LK $ IVAR VOID))
>                                              (ICONST UNIT))]))
>                     (PAIR (IPROD (IVAR VOID) (IPROD (IVAR VOID) (ICONST UNIT)))
>                      VOID)))))))
>   idescFakeREF :: REF
>   idescFakeREF = [("Primitive", 0), ("IDesc", 0)] 
>                    := (FAKE :<: ARR SET (ARR UNIT SET))
>   idesc :: VAL
>   idesc = L $ "I" :. [._I. LK $
>             IMU (Just (N ((P idescFakeREF) :$ A (NV _I)))) 
>                  UNIT (inIDesc -$ [ NV _I]) VOID ]
>
>   idescREF :: REF
>   idescREF = [("Primitive", 0), ("IDesc", 0)] 
>                := (DEFN idesc :<: ARR SET (ARR UNIT SET))
>
>   idescDREF :: REF
>   idescDREF = [("Primitive", 0), ("IDescD", 0)] 
>                 := (DEFN inIDesc 
>                      :<: ARR SET (ARR UNIT (idesc $$ A UNIT $$ A VOID)))


>   sumilike :: VAL -> VAL -> Maybe (VAL, VAL -> VAL)
>   sumilike _I (IFSIGMA e b)  = 
>       Just (e, \t -> switchOp @@ [ e , t , LK (idesc $$ A _I $$ A VOID), b ])
>   sumilike _ _               = Nothing





>   icaseREF :: REF
>   icaseREF = [("Primitive", 0), ("icase", 0)] := (DEFN cdef :<: cty) 

>   idindREF :: REF
>   idindREF = [("Primitive", 0), ("idind", 0)] := (DEFN idef :<: ity) 


We build a case gadget for idata, the haskell code below is generated from 
this Cochon command - some sort of Prelude is really in order here, the
question is how to go about bootstrapping it...

\begin{verbatim}
make case :=  \ iI e cs i x pP p -> iinduction iI (\ j -> con ['fsigmaD , [e (cs j)] ]) i x pP (\ j y _ -> switch e (y !) (\ t -> ((k : iI)(xs : idesc iI (switch e t (\ u -> IDesc iI []) (cs k)) (\ l -> IMu iI (\ m -> con ['fsigmaD , [e (cs m)] ]) l)) -> pP [k , con [t , xs]])) p j (y -))
          : (iI : Set) (e : EnumU) (cs : iI -> branches e (\ u -> IDesc iI []))
             (i : iI) (x : IMu iI (\ j -> con ['fsigmaD , [e (cs j)] ]) i)
              (pP : Sig (j : iI ; IMu iI (\ k -> con ['fsigmaD , [e (cs k)] ]) j) -> Set)
               (p : branches e
                      (\ t -> (j : iI) ->
                         (xs : idesc iI (switch e t (\ u -> IDesc iI []) (cs j))
                                 (\ k -> IMu iI (\ l -> con ['fsigmaD , [e (cs l)] ]) k))
                      -> pP [ j , con [ t , xs ] ]))
                 -> pP [ i , x ] ;
\end{verbatim}

Using this enables us to avoid the enum splitting we currently do.

>   cty  = (PI SET (L $ "I" :. [.iI. (PI (MU (Just (ANCHOR (TAG "EnumU")
>     SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT
>     (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID))))) (PAIR (L $
>     "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE) (PAIR (TAG "nil")
>     (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID))
>     VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU
>     (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))]) VOID))))) (L $ "e"
>     :. [.e. (PI (ARR (NV iI) (N (branchesOp :@ [(NV e), (L $ "u" :. [.u.
>     (IMU (Just (N (P idescREF :$ (A (NV iI))))) UNIT (LK (CON (PAIR (SU (SU
>     (SU (SU (SU ZE))))) (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR
>     (CON (PAIR (SU ZE) (PAIR (TAG "constD") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "piD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "fsigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON
>     (PAIR ZE VOID)) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID))))
>     VOID)))) (PAIR (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI)
>     (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID)))) (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON
>     (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR
>     (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE
>     VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID))))
>     VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU
>     (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT
>     (NV eE)) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR
>     (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON
>     (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE))
>     (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU")
>     SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT
>     (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID))))) (PAIR (L $
>     "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE) (PAIR (TAG "nil")
>     (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID))
>     VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU
>     (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))]) VOID))))) (PAIR (L
>     $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR (SU (SU (SU ZE))) (PAIR (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR
>     VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID)))
>     VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE))))))
>     (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     (SU (SU ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID)))) VOID)))) VOID)))))))
>     VOID))))) VOID)])]))) (L $ "cs" :. [.cs. (PI (NV iI) (L $ "i" :. [.i.
>     (PI (IMU Nothing (NV iI) (L $ "j" :. [.j. (CON (PAIR (SU (SU (SU (SU
>     (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV j)))) VOID))))])
>     (NV i)) (L $ "x" :. [.x. (PI (ARR (SIGMA (NV iI) (L $ "j" :.  [.j. (IMU
>     Nothing (NV iI) (L $ "k" :. [.k. (CON (PAIR (SU (SU (SU (SU (SU ZE)))))
>     (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV k)))) VOID))))]) (NV j))]))
>     SET) (L $ "P" :. [.pP. (PI (N (branchesOp :@ [(NV e), (L $ "t" :. [.t.
>     (PI (NV iI) (L $ "j" :. [.j.  (PI (N (idescOp :@ [(NV iI), (N (switchOp
>     :@ [(NV e), (NV t), (L $ "u" :. [.u. (IMU (Just (N (P idescREF :$ (A
>     (NV iI))))) UNIT (LK (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "piD") (PAIR (CON (PAIR
>     (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :.
>     [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU
>     (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just
>     (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :.  [.c. (N (switchDOp :@
>     [(CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON
>     (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID)))))
>     VOID)))) VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE.  (CON
>     (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU
>     ZE))) (PAIR (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU
>     ZE) (PAIR UNIT VOID))) VOID)))) VOID)))) VOID))))))) VOID))))) VOID)]),
>     (N ((V cs) :$ (A (NV j))))])), (L $ "k" :. [.k. (IMU Nothing (NV iI) (L
>     $ "l" :. [.l. (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR
>     (N ((V cs) :$ (A (NV l)))) VOID))))]) (NV k))])])) (L $ "xs" :. [.xs.
>     (N ((V pP) :$ (A (PAIR (NV j) (CON (PAIR (NV t) (NV
>     xs)))))))]))]))])])) (L $ "p" :. [.p. (N ((V pP) :$ (A (PAIR (NV i) (NV
>     x)))))]))]))]))]))]))]))]))


>   cdef = (L $ "I" :. [.iI. (L $ "e" :. [.e. (L $ "cs" :. [.cs. (L $ "i"
>     :. [.i. (L $ "x" :. [.x. (L $ "P" :. [.pP. (L $ "p" :. [.p. (N
>     (iinductionOp :@ [(NV iI), (L $ "j" :. [.j. (CON (PAIR (SU (SU (SU (SU
>     (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV j)))) VOID))))]),
>     (NV i), (NV x), (NV pP), (L $ "j" :. [.j. (L $ "y" :. [.y. (LK (N
>     (((switchOp :@ [(NV e), (N ((V y) :$ Fst)), (L $ "t" :. [.t. (PI (NV
>     iI) (L $ "k" :. [.k. (PI (N (idescOp :@ [(NV iI), (N (switchOp :@ [(NV
>     e), (NV t), (L $ "u" :. [.u. (IMU (Just (N (P idescREF :$ (A (NV
>     iI))))) UNIT (LK (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "piD") (PAIR (CON (PAIR
>     (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :.
>     [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU
>     (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just
>     (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :.  [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE.  (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON
>     (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR
>     (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE
>     VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID))))
>     VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU
>     (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU ZE))) (PAIR
>     (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR
>     (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID)))
>     (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE
>     (PAIR VOID VOID))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))
>     VOID)))) VOID))))))) VOID))))) VOID)]), (N ((V cs) :$ (A (NV k))))])),
>     (L $ "l" :. [.l. (IMU Nothing (NV iI) (L $ "m" :. [.m. (CON (PAIR (SU
>     (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV m))))
>     VOID))))]) (NV l))])])) (L $ "xs" :. [.xs. (N ((V pP) :$ (A (PAIR (NV
>     k) (CON (PAIR (NV t) (NV xs)))))))]))]))]), (NV p)]) :$ (A (NV j))) :$
>     (A (N ((V y) :$ Snd))))))])])]))])])])])])])])

Same for induction, based on this def:

\begin{verbatim}
make dind :=  \ iI e cs i x pP p -> iinduction iI (\ j -> con ['fsigmaD , [e (cs j)] ]) i x pP (\ j y h -> switch e (y !) (\ t -> ((k : iI)(xs : idesc iI (switch e t (\ u -> IDesc iI []) (cs k)) (\ l -> IMu iI (\ m -> con ['fsigmaD , [e (cs m)] ]) l))(hs : idesc (Sig (l : iI ; IMu iI (\ m -> con ['fsigmaD , [e (cs m)] ]) l)) (ibox iI (switch e t (\ u -> IDesc iI []) (cs k)) (\ l -> IMu iI (\ m -> con ['fsigmaD , [e (cs m)] ]) l) xs) pP) -> pP [k , con [t , xs]])) p j (y -) h)
          : (iI : Set) (e : EnumU) (cs : iI -> branches e (\ u -> IDesc iI [])) 
             (i : iI) (x : IMu iI (\ j -> con ['fsigmaD , [e (cs j)] ]) i) 
              (pP : Sig (j : iI ; IMu iI (\ k -> con ['fsigmaD , [e (cs k)] ]) j) -> Set) 
               (p : branches e 
                      (\ t -> (j : iI) ->
                         (xs : idesc iI (switch e t (\ u -> IDesc iI []) (cs j)) (\ k -> IMu iI (\ l -> con ['fsigmaD , [e (cs l)] ]) k)) 
                         (hs : idesc (Sig (k : iI ; IMu iI (\ l -> con ['fsigmaD , [e (cs l)] ]) k)) (ibox iI (switch e t (\ u -> IDesc iI []) (cs j)) (\ k -> IMu iI (\ l -> con ['fsigmaD , [e (cs l)] ]) k) xs) pP) 
                      -> pP [ j , con [ t , xs ] ]))
                 -> pP [ i , x ] ;
\end{verbatim}

>   ity   = (PI SET (L $ "I" :. [.iI. (PI (MU (Just (ANCHOR (TAG "EnumU")
>     SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT
>     (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID))))) (PAIR (L $
>     "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE) (PAIR (TAG "nil")
>     (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID))
>     VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU
>     (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))]) VOID))))) (L $ "e"
>     :. [.e. (PI (ARR (NV iI) (N (branchesOp :@ [(NV e), (L $ "u" :. [.u.
>     (IMU (Just (N (P idescREF :$ (A (NV iI))))) UNIT (LK (CON (PAIR (SU (SU
>     (SU (SU (SU ZE))))) (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR
>     (CON (PAIR (SU ZE) (PAIR (TAG "constD") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "piD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "fsigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON
>     (PAIR ZE VOID)) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID))))
>     VOID)))) (PAIR (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI)
>     (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID)))) (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON
>     (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR
>     (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE
>     VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID))))
>     VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU
>     (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT
>     (NV eE)) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR
>     (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON
>     (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE))
>     (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU")
>     SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT
>     (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID))))) (PAIR (L $
>     "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE) (PAIR (TAG "nil")
>     (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID))
>     VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR
>     (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU
>     (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))]) VOID))))) (PAIR (L
>     $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR (SU (SU (SU ZE))) (PAIR (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR
>     VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID)))
>     VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE))))))
>     (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     (SU (SU ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID)))) VOID)))) VOID)))))))
>     VOID))))) VOID)])]))) (L $ "cs" :. [.cs. (PI (NV iI) (L $ "i" :. [.i.
>     (PI (IMU Nothing (NV iI) (L $ "j" :. [.j. (CON (PAIR (SU (SU (SU (SU
>     (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV j)))) VOID))))])
>     (NV i)) (L $ "x" :. [.x. (PI (ARR (SIGMA (NV iI) (L $ "j" :.  [.j. (IMU
>     Nothing (NV iI) (L $ "k" :. [.k. (CON (PAIR (SU (SU (SU (SU (SU ZE)))))
>     (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV k)))) VOID))))]) (NV j))]))
>     SET) (L $ "P" :. [.pP. (PI (N (branchesOp :@ [(NV e), (L $ "t" :. [.t.
>     (PI (NV iI) (L $ "j" :. [.j.  (PI (N (idescOp :@ [(NV iI), (N (switchOp
>     :@ [(NV e), (NV t), (L $ "u" :. [.u. (IMU (Just (N (P idescREF :$ (A
>     (NV iI))))) UNIT (LK (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "piD") (PAIR (CON (PAIR
>     (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :.
>     [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU
>     (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just
>     (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :.  [.c. (N (switchDOp :@
>     [(CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON
>     (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID)))))
>     VOID)))) VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE.  (CON
>     (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU
>     ZE))) (PAIR (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU
>     ZE) (PAIR UNIT VOID))) VOID)))) VOID)))) VOID))))))) VOID))))) VOID)]),
>     (N ((V cs) :$ (A (NV j))))])), (L $ "k" :. [.k. (IMU Nothing (NV iI) (L
>     $ "l" :. [.l. (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR
>     (N ((V cs) :$ (A (NV l)))) VOID))))]) (NV k))])])) (L $ "xs" :. [.xs.
>     (PI (N (idescOp :@ [(SIGMA (NV iI) (L $ "k" :. [.k. (IMU Nothing (NV
>     iI) (L $ "l" :. [.l. (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (NV
>     e) (PAIR (N ((V cs) :$ (A (NV l)))) VOID))))]) (NV k))])), (N (iboxOp
>     :@ [(NV iI), (N (switchOp :@ [(NV e), (NV t), (L $ "u" :. [.u. (IMU
>     (Just (N (P idescREF :$ (A (NV iI))))) UNIT (LK (CON (PAIR (SU (SU (SU
>     (SU (SU ZE))))) (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "piD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU
>     ZE) (PAIR (TAG "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD")
>     (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU
>     (SU ZE)))) (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $
>     "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID
>     VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID)))
>     VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU
>     (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU
>     (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :.  [.c. (N (switchDOp :@
>     [(CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR
>     (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON
>     (PAIR ZE VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID)))))
>     VOID)))) VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE.  (CON
>     (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU
>     ZE))) (PAIR (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON
>     (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID))) (PAIR (CON (PAIR (SU
>     ZE) (PAIR UNIT VOID))) VOID)))) VOID)))) VOID))))))) VOID))))) VOID)]),
>     (N ((V cs) :$ (A (NV j))))])), (L $ "k" :. [.k. (IMU Nothing (NV iI) (L
>     $ "l" :. [.l. (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR
>     (N ((V cs) :$ (A (NV l)))) VOID))))]) (NV k))]), (NV xs)])), (NV pP)]))
>     (L $ "hs" :. [.hs. (N ((V pP) :$ (A (PAIR (NV j) (CON (PAIR (NV t) (NV
>     xs)))))))]))]))]))])])) (L $ "p" :. [.p.  (N ((V pP) :$ (A (PAIR (NV i)
>     (NV x)))))]))]))]))]))]))]))]))


>   idef  = (L $ "I" :. [.iI. (L $ "e" :. [.e. (L $ "cs" :. [.cs. (L $ "i"
>     :. [.i. (L $ "x" :. [.x. (L $ "P" :. [.pP. (L $ "p" :. [.p. (N
>     (iinductionOp :@ [(NV iI), (L $ "j" :. [.j. (CON (PAIR (SU (SU (SU (SU
>     (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV j)))) VOID))))]),
>     (NV i), (NV x), (NV pP), (L $ "j" :. [.j. (L $ "y" :. [.y. (L $ "h" :.
>     [.h. (N ((((switchOp :@ [(NV e), (N ((V y) :$ Fst)), (L $ "t" :. [.t.
>     (PI (NV iI) (L $ "k" :. [.k. (PI (N (idescOp :@ [(NV iI), (N (switchOp
>     :@ [(NV e), (NV t), (L $ "u" :. [.u. (IMU (Just (N (P idescREF :$ (A
>     (NV iI))))) UNIT (LK (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "piD") (PAIR (CON (PAIR
>     (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :.
>     [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU
>     (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just
>     (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON
>     (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR
>     (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE
>     VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID))))
>     VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU
>     (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU ZE))) (PAIR
>     (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR
>     (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID)))
>     (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE
>     (PAIR VOID VOID))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))
>     VOID)))) VOID))))))) VOID))))) VOID)]), (N ((V cs) :$ (A (NV k))))])),
>     (L $ "l" :. [.l. (IMU Nothing (NV iI) (L $ "m" :. [.m. (CON (PAIR (SU
>     (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV m))))
>     VOID))))]) (NV l))])])) (L $ "xs" :. [.xs. (PI (N (idescOp :@ [(SIGMA
>     (NV iI) (L $ "l" :. [.l. (IMU Nothing (NV iI) (L $ "m" :. [.m. (CON
>     (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A
>     (NV m)))) VOID))))]) (NV l))])), (N (iboxOp :@ [(NV iI), (N (switchOp
>     :@ [(NV e), (NV t), (L $ "u" :. [.u. (IMU (Just (N (P idescREF :$ (A
>     (NV iI))))) UNIT (LK (CON (PAIR (SU (SU (SU (SU (SU ZE))))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "varD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "constD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "piD") (PAIR (CON (PAIR
>     (SU ZE) (PAIR (TAG "fpiD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "sigmaD") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "fsigmaD") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "prodD") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) VOID)))) (PAIR (PAIR (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (NV iI) (PAIR (LK (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID)))) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR SET (PAIR (LK (CON (PAIR (SU ZE) (PAIR UNIT VOID)))) VOID))))
>     (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR SET (PAIR (L $ "S" :.
>     [.sS. (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU
>     (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID))))
>     VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))])
>     VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR (MU (Just
>     (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON
>     (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE VOID)) VOID))))
>     VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON (PAIR (SU ZE)
>     (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR
>     (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR UID (PAIR
>     (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE VOID)) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID)))) VOID)), (NV c)]))])
>     VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU (SU (SU (SU (SU (SU
>     ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (ENUMT (NV eE)) (PAIR (LK
>     (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE)
>     (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR SET (PAIR (L $ "S" :. [.sS. (CON (PAIR (SU (SU (SU (SU (SU
>     (SU ZE)))))) (PAIR (CON (PAIR (SU (SU ZE)) (PAIR (NV sS) (PAIR (LK (CON
>     (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON (PAIR (SU ZE) (PAIR
>     UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR (SU (SU (SU (SU
>     ZE)))) (PAIR (MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) (CON
>     (PAIR (SU (SU (SU (SU ZE)))) (PAIR (ENUMT (CON (PAIR (SU ZE) (PAIR (TAG
>     "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG "cons") (PAIR (CON (PAIR ZE
>     VOID)) VOID)))) VOID))))) (PAIR (L $ "c" :. [.c. (N (switchDOp :@ [(CON
>     (PAIR (SU ZE) (PAIR (TAG "nil") (PAIR (CON (PAIR (SU ZE) (PAIR (TAG
>     "cons") (PAIR (CON (PAIR ZE VOID)) VOID)))) VOID)))), (PAIR (CON (PAIR
>     (SU ZE) (PAIR UNIT VOID))) (PAIR (CON (PAIR (SU (SU (SU (SU ZE))))
>     (PAIR UID (PAIR (LK (CON (PAIR (SU (SU (SU ZE))) (PAIR (CON (PAIR ZE
>     VOID)) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))) VOID))))
>     VOID)), (NV c)]))]) VOID))))) (PAIR (L $ "E" :. [.eE. (CON (PAIR (SU
>     (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR (SU (SU (SU ZE))) (PAIR
>     (NV eE) (PAIR (LK (CON (PAIR ZE (PAIR VOID VOID)))) VOID)))) (PAIR (CON
>     (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))]) VOID)))) (PAIR (CON (PAIR
>     (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE (PAIR VOID VOID)))
>     (PAIR (CON (PAIR (SU (SU (SU (SU (SU (SU ZE)))))) (PAIR (CON (PAIR ZE
>     (PAIR VOID VOID))) (PAIR (CON (PAIR (SU ZE) (PAIR UNIT VOID))) VOID))))
>     VOID)))) VOID))))))) VOID))))) VOID)]), (N ((V cs) :$ (A (NV k))))])),
>     (L $ "l" :. [.l. (IMU Nothing (NV iI) (L $ "m" :. [.m. (CON (PAIR (SU
>     (SU (SU (SU (SU ZE))))) (PAIR (NV e) (PAIR (N ((V cs) :$ (A (NV m))))
>     VOID))))]) (NV l))]), (NV xs)])), (NV pP)])) (L $ "hs" :.  [.hs. (N ((V
>     pP) :$ (A (PAIR (NV k) (CON (PAIR (NV t) (NV xs)))))))]))]))]))]), (NV
>     p)]) :$ (A (NV j))) :$ (A (N ((V y) :$ Snd)))) :$ (A (NV
>     h))))])])])]))])])])])])])])
