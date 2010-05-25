\section{IDesc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.IDesc where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where
>   IDesc   :: t -> Can t
>   IMu     :: Labelled (Id :*: Id) t -> t -> Can t
>   IVar     :: t -> Can t
>   IPi     :: t -> t -> Can t
>   IFPi     :: t -> t -> Can t
>   ISigma  :: t -> t -> Can t
>   IFSigma  :: t -> t -> Can t
>   IConst   :: t -> Can t
>   IProd   :: t -> t -> Can t

> import -> CanTyRules where
>   canTy chev (Set :>: IMu (ml :?=: (Id ii :& Id x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (IDESC iiv) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ IMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
>   canTy chev (IMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>     yyv <- chev (idescOp @@ [ ii
>                             , x $$ A i 
>                             , L $ HF "i" $ \i -> C (IMu tt i)
>                             ] :>: y)
>     return $ Con yyv
>   canTy chev (Set :>: IDesc ii) = 
>     (|IDesc (chev (SET :>: ii))|)
>   canTy chev (IDesc _I :>: IVar i) = do
>     iiv@(i :=>: iv) <- chev (_I :>: i)
>     return $ IVar iiv
>   canTy chev (IDesc _I :>: IPi s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv (IDESC _I) :>: t)
>     return $ IPi ssv ttv
>   canTy chev (IDesc _I :>: IFPi e f) = do
>     eev@(e :=>: ev) <- chev (enumU :>: e)
>     ffv@(f :=>: fv) <- chev (ARR (ENUMT ev) (IDESC _I) :>: f)
>     return $ IFPi eev ffv
>   canTy chev (IDesc _I :>: ISigma s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv (IDESC _I) :>: t)
>     return $ ISigma ssv ttv
>   canTy chev (IDesc _I :>: IFSigma e b) = do
>     eev@(e :=>: ev) <- chev (enumU :>: e)
>     bbv@(b :=>: bv) <- chev (branchesOp @@ [ ev
>                                            , L (K (IDESC _I))] :>: b)
>     return $ IFSigma eev bbv
>   canTy chev (IDesc _I :>: IConst k) = do
>     kkv@(k :=>: kv) <- chev (SET :>: k)
>     return $ IConst kkv
>   canTy chev (IDesc _I :>: IProd x y) = do
>     xxv@(x :=>: xv) <- chev (IDESC _I :>: x)
>     yyv@(y :=>: yv) <- chev (IDESC _I :>: y)
>     return $ IProd xxv yyv

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where
>   pattern IDESC i = C (IDesc i)
>   pattern IMU l ii x i = C (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern IVAR i = C (IVar i)
>   pattern IPI s t = C (IPi s t)
>   pattern IFPI s t = C (IFPi s t)
>   pattern ISIGMA s t = C (ISigma s t)
>   pattern IFSIGMA s t = C (IFSigma s t)
>   pattern ICONST p = C (IConst p)
>   pattern IPROD x y = C (IProd x y)

> import -> CanDisplayPats where
>   pattern DIDESC i = DC (IDesc i)
>   pattern DIMU l ii x i = DC (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern DIVAR i = DC (IVar i)
>   pattern DIPI s t = DC (IPi s t)
>   pattern DIFPI s t = DC (IFPi s t)
>   pattern DISIGMA s t = DC (ISigma s t)
>   pattern DIFSIGMA s t = DC (IFSigma s t)
>   pattern DICONST p = DC (IConst p)
>   pattern DIPROD x y = DC (IProd x y)

> import -> CanPretty where
>   pretty (IDesc ii) = wrapDoc (kword KwIDesc <+> pretty ii ArgSize) ArgSize
>   pretty (IMu (Just l   :?=: _) i)  = wrapDoc
>       (pretty l AppSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>       (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IVar i) = wrapDoc
>       (kword KwIVar <+> pretty i ArgSize)
>       ArgSize
>   pretty (IPi s t) = wrapDoc
>       (kword KwIPi <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IFPi s t) = wrapDoc
>       (kword KwIFPi <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (ISigma s t) = wrapDoc
>       (kword KwISigma <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IFSigma s t) = wrapDoc
>       (kword KwIFSigma <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IConst i) = wrapDoc
>       (kword KwIConst <+> pretty i ArgSize)
>       ArgSize
>   pretty (IProd x y) = wrapDoc
>       (kword KwIProd <+> pretty x ArgSize <+> pretty y ArgSize)
>       ArgSize

> import -> CanTraverse where
>   traverse f (IDesc i)     = (|IDesc (f i)|)
>   traverse f (IMu l i)     = (|IMu (traverse f l) (f i)|)
>   traverse f (IVar i)       = (|IVar (f i)|)
>   traverse f (IPi s t)     = (|IPi (f s) (f t)|)
>   traverse f (IFPi s t)     = (|IFPi (f s) (f t)|)
>   traverse f (ISigma s t)  = (|ISigma (f s) (f t)|)
>   traverse f (IFSigma s t) = (|IFSigma (f s) (f t)|)
>   traverse f (IConst p)     = (|IConst (f p)|)
>   traverse f (IProd x y)   = (|IProd (f x) (f y)|)

> import -> CanHalfZip where
>   halfZip (IDesc i0) (IDesc i1) = (|(IDesc (i0,i1))|)
>   halfZip (IMu l0 i0) (IMu l1 i1) = (|(\p -> IMu p (i0,i1)) (halfZip l0 l1)|)
>   halfZip (IVar i0) (IVar i1) = (|(IVar (i0,i1))|)
>   halfZip (IPi s0 t0) (IPi s1 t1) = (|(IPi (s0,s1) (t0,t1))|)
>   halfZip (IFPi s0 t0) (IFPi s1 t1) = (|(IFPi (s0,s1) (t0,t1))|)
>   halfZip (ISigma s0 t0) (ISigma s1 t1) = (|(ISigma (s0,s1) (t0,t1))|)
>   halfZip (IFSigma s0 t0) (IFSigma s1 t1) = (|(IFSigma (s0,s1) (t0,t1))|)
>   halfZip (IConst p0) (IConst p1) = (|(IConst (p0,p1))|)
>   halfZip (IProd s0 t0) (IProd s1 t1) = (|(IProd (s0,s1) (t0,t1))|)


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
>                 "d" :<: ARR iI (IDESC iI) :-: \d ->
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
>                 "d" :<: ARR iI (IDESC iI) :-: \d ->
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
>   coerce (IDesc (d0, d1)) q x = Right x


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
>     case arg of      
>       IVAR i       -> Right $ ivarC i
>       IPI s t      -> Right $ ipiC s t 
>       IFPI s t     -> Right $ ifpiC s t
>       ISIGMA s t   -> Right $ isigmaC s t
>       IFSIGMA s t  -> Right $ ifsigmaC s t
>       ICONST k     -> Right $ iconstC k
>       IPROD x y    -> Right $ iprodC x y
>       N t     -> Left t

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
>        "d" :<: IDESC iI :-: \d ->
>        "X" :<: ARR iI SET :-: \x ->
>        Target SET
>       idOpRun :: [VAL] -> Either NEU VAL
>       idOpRun [_I, _D, _P] = 
>         mkLazyIDescDef _D  (  ivarD _I _P
>                            ,  ipiD _I _P        
>                            ,  ifpiD _I _P        
>                            ,  isigmaD _I _P        
>                            ,  ifsigmaD _I _P        
>                            ,  iconstD _I _P        
>                            ,  iprodD _I _P  
>                            )
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
>                                                      , L (K (IDESC _I))
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
>         "I" :<: SET                    :-: \ _I ->
>         "D" :<: IDESC _I               :-: \ _D ->
>         "P" :<: ARR _I SET             :-: \ _P ->
>         "v" :<: idescOp @@ [_I,_D,_P]  :-: \v ->
>         Target $ IDESC (SIGMA _I (L . HF "i" $ \i -> _P $$ A i))
>       iboxOpRun :: [VAL] -> Either NEU VAL
>       iboxOpRun [_I,_D,_P,v] = 
>         mkLazyIDescDef _D  (  ivarD _I _P v
>                            ,  ipiD _I _P v       
>                            ,  ifpiD _I _P v       
>                            ,  isigmaD _I _P v        
>                            ,  ifsigmaD _I _P v       
>                            ,  iconstD _I _P v       
>                            ,  iprodD _I _P v 
>                            )
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
>                                    , L (K (IDESC _I))
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
>         "D" :<: IDESC _I :-: \ _D ->
>         "X" :<: ARR _I SET :-: \ _X -> 
>         let _IX = SIGMA _I (L . HF "i" $ \i -> _X $$ A i) in
>         "P" :<: ARR _IX SET :-: \ _P ->
>         "p" :<: (pity $ "ix" :<: _IX :-: \ ix -> Target $ _P $$ A ix) :-: \ _ ->
>         "v" :<: (idescOp @@ [_I,_D,_X]) :-: \v ->
>          Target (idescOp @@ [_IX, iboxOp @@ [_I,_D,_X,v], _P])
>       imapBoxOpRun :: [VAL] -> Either NEU VAL
>       imapBoxOpRun [_I, _D, _X, _P, p, v]  = 
>         mkLazyIDescDef _D (varD _I _X _P p v, 
>                            piD _I _X _P p v,
>                            fpiD _I _X _P p v,
>                            sigmaD _I _X _P p v,
>                            fsigmaD _I _X _P p v,
>                            constD _I _X _P p v, 
>                            prodD _I _X _P p v) 
>       varD _I _X _P p v i = p $$ A (PAIR i v)
>       piD _I _X _P p v _S _T = 
>         L . HF "s" $ \s -> imapBoxOp @@ [_I,_T $$ A s,_X,_P,p,v $$ A s]
>       fpiD _I _X _P p v _E _Df = 
>         L . HF "s" $ \s -> imapBoxOp @@ [_I,_Df $$ A s,_X,_P,p,v $$ A s]
>       sigmaD _I _X _P p v _S _T = imapBoxOp @@ [_I,_T $$ A (v $$ Fst),_X,_P,p,v $$ Snd]
>       fsigmaD _I _X _P p v _E _Ds =
>         imapBoxOp @@ [_I,switchOp @@ [_E,v $$ Fst,L (K (IDESC _I)),_Ds],_X,_P,p,v $$ Snd]
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
>         "D" :<: ARR _I (IDESC _I) :-: \_D ->
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
>   KwIDesc :: Keyword
>   KwIVar :: Keyword
>   KwIPi :: Keyword
>   KwIFPi :: Keyword
>   KwISigma :: Keyword
>   KwIFSigma :: Keyword
>   KwIConst :: Keyword
>   KwIProd :: Keyword

> import -> KeywordTable where
>   key KwIMu      = "IMu"
>   key KwIDesc    = "IDesc"
>   key KwIVar     = "IVar"
>   key KwIPi      = "IPi"
>   key KwIFPi     = "IFPi"
>   key KwISigma   = "ISigma"
>   key KwIFSigma  = "IFSigma"
>   key KwIConst   = "IConst"
>   key KwIProd    = "IProd"

> import -> InDTmParsersSpecial where
>   (AndSize, (|(DIMU Nothing) (%keyword KwIMu%) (sizedInDTm ArgSize) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIDESC (%keyword KwIDesc%) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIVAR (%keyword KwIVar%) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIPI (%keyword KwIPi%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIFPI (%keyword KwIFPi%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DISIGMA (%keyword KwISigma%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIFSIGMA (%keyword KwIFSigma%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DICONST (%keyword KwIConst%) (sizedInDTm ArgSize)|)) :
>   (AndSize, (|DIPROD (%keyword KwIProd%) (sizedInDTm ArgSize) (sizedInDTm ArgSize)|)) :


Just like |Mu|, when elaborating |IMu| we attach a display label if the
description is not neutral, to improve the pretty-printed representation.

> import -> MakeElabRules where
>   makeElab' loc (SET :>: DIMU Nothing iI d i) = do
>       (r,sp) <- eFake
>       let l = (P r) $:$ (init sp)
>       iI  :=>: iIv  <- subElab loc (SET :>: iI)
>       d   :=>: dv   <- subElab loc (ARR iIv (IDESC iIv) :>: d)
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
>       makeElab' loc (ty :>: DCON (DPAIR (DTAG s) (fold xs)))
>     where fold :: [InDTmRN] -> InDTmRN
>           fold [] = DVOID
>           fold [x] = x
>           fold (x : xs) = DPAIR x (fold xs)

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
>         unfold :: InDTmRN -> [InDTmRN]
>         unfold DVOID        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]
>         sumilike :: VAL -> VAL -> Maybe (VAL, VAL -> VAL)
>         sumilike _I (IFSIGMA e b)  = 
>           Just (e, \t -> switchOp @@ [ e , t , L (K (IDESC _I)), b ])
>         sumilike _ _               = Nothing

> import -> InDTmConstructors where

> import -> InDTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
