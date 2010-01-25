\section{IDesc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.IDesc where

%endif

> import -> CanConstructors where
>   IDesc   :: t -> Can t
>   IMu     :: Labelled (Id :*: Id) t -> t -> Can t
>   IDone   :: t -> Can t
>   IArg    :: t -> t -> Can t
>   IInd1   :: t -> t -> Can t
>   IInd    :: t -> t -> t -> Can t

> import -> TraverseCan where
>   traverse f (IDesc i) = (|IDesc (f i)|)
>   traverse f (IMu l i) = (|IMu (traverse f l) (f i)|)
>   traverse f (IDone p) = (|IDone (f p)|)
>   traverse f (IArg a d) = (|IArg (f a) (f d)|)
>   traverse f (IInd1 x y) = (|IInd1 (f x) (f y)|)
>   traverse f (IInd x y z) = (|IInd (f x) (f y) (f z)|)

> import -> HalfZipCan where
>   halfZip (IDesc i0) (IDesc i1) = (|(IDesc (i0,i1))|)
>   halfZip (IMu l0 i0) (IMu l1 i1) = (|(\p -> IMu p (i0,i1)) (halfZip l0 l1)|)
>   halfZip (IDone p0) (IDone p1) = (|(IDone (p0,p1))|)
>   halfZip (IArg a0 d0) (IArg a1 d1) = (|(IArg (a0,a1) (d0,d1))|)
>   halfZip (IInd1 x0 y0) (IInd1 x1 y1) = (|(IInd1 (x0,x1) (y0,y1))|)
>   halfZip (IInd x0 y0 z0) (IInd x1 y1 z1) = (|(IInd (x0,x1) (y0,y1) (z0,z1))|)

> import -> CanPats where
>   pattern IDESC i = C (IDesc i)
>   pattern IMU l ii x i = C (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern IDONE p = C (IDone p) 
>   pattern IARG s d = C (IArg s d) 
>   pattern IIND h hi d = C (IInd h hi d) 
>   pattern IIND1 i d = C (IInd1 i d) 

> import -> DisplayCanPats where
>   pattern DIDESC i = DC (IDesc i)
>   pattern DIMU l ii x i = DC (IMu (l :?=: (Id ii :& Id x)) i) 
>   pattern DIDONE p = DC (IDone p) 
>   pattern DIARG s d = DC (IArg s d) 
>   pattern DIIND h hi d = DC (IInd h hi d) 
>   pattern DIIND1 i d = DC (IInd1 i d) 

> import -> SugarTactics where
>   dmuTac ii t i = can $ IMu (Nothing :?=: (Id ii :& Id t)) i
>   dmuTacL l i = can $ IMu l i
>   idescTac i = can $ IDesc i 
>   ddoneTac p = can $ IDone p 
>   dargTac x y = can $ IArg x y 
>   dindTac x y z = can $ IInd x y z 
>   dind1Tac x y = can $ IInd1 x y 

> import -> CanTyRules where
>   canTy chev (Set :>: IMu (ml :?=: (Id ii :& Id x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (IDESC iiv) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ IMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
>   canTy chev (IMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>     yyv <- chev (idescOp @@ [ ii
>                            , x $$ A i 
>                            , L $ HF "i" $ \i -> C (IMu tt i)
>                            ] :>: y)
>     return $ Con yyv
>   canTy chev (Set :>: IDesc ii) = 
>     (|IDesc (chev (SET :>: ii))|)
>   canTy chev (IDesc ii :>: IDone p) =  
>     (|IDone (chev (PROP :>: p))|)
>   canTy chev (IDesc ii :>: IArg a d) = do
>     aav@(a :=>: av) <- chev (SET :>: a)  
>     ddv <- chev (ARR av (IDESC ii) :>: d)
>     (|(IArg aav ddv)|)  
>   canTy chev (IDesc ii :>: IInd1 i d) =
>     (|IInd1 (chev (ii :>: i)) (chev (IDESC ii :>: d))|)  
>   canTy chev (IDesc ii :>: IInd h hi d) = do
>     hhv@(h :=>: hv) <- chev (SET :>: h)
>     hihiv@(hi :=>: hiv) <- chev (ARR hv ii :>: hi)
>     ddv <- chev (IDESC ii :>: d)
>     (|(IInd hhv hihiv ddv)|)  

> import -> Coerce where
>   -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
>   coerce (IMu (Just (l0,l1) :?=: (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) = 
>     let ql  = CON $ q $$ Fst
>         qiI = CON $ q $$ Snd $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Snd $$ Fst
>         (typ :>: vap) = laty ("I" :<: SET :-: \iI ->
>                               "d" :<: ARR iI (IDESC iI) :-: \d ->
>                               "i" :<: iI :-: \i ->
>                               "l" :<: ARR iI SET :-: \l ->
>                               Target (SET :>: 
>                                        N (idescOp :@ [ iI , d $$ A i
>                                                      , L $ HF "i" $ IMU (|l|) iI d
>                                                      ]))) 
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0 , L $ HF "i" $ IMU (|l0|) iI0 d0 ] 
>              , idescOp @@ [ iI1 , d1 $$ A i1 , L $ HF "i" $ IMU (|l1|) iI1 d1 ] 
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
>         (typ :>: vap) = laty ("I" :<: SET :-: \iI ->
>                               "d" :<: ARR iI (IDESC iI) :-: \d ->
>                               "i" :<: iI :-: \i ->
>                               Target (SET :>: 
>                                        N (idescOp :@ [ iI , d $$ A i
>                                                      , L $ HF "i" $ IMU Nothing iI d
>                                                      ]))) 
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0 , L $ HF "i" $ IMU Nothing iI0 d0 ] 
>              , idescOp @@ [ iI1 , d1 $$ A i1 , L $ HF "i" $ IMU Nothing iI1 d1 ] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>              , x ]


> import -> CanPretty where
>   pretty (IDesc ii) = wrapDoc (kword KwIDesc <+> pretty ii ArgSize) ArgSize
>   pretty (IMu (Just l   :?=: _) i)  = wrapDoc
>       (pretty l ArgSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>       (kword KwIMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IDone p) = wrapDoc
>       (kword KwIDone <+> pretty p ArgSize)
>       ArgSize
>   pretty (IArg a d) = wrapDoc
>       (kword KwIArg <+> pretty a ArgSize <+> pretty d ArgSize)
>       ArgSize
>   pretty (IInd1 i d) = wrapDoc
>       (kword KwIInd1 <+> pretty i ArgSize <+> pretty d ArgSize)
>       ArgSize
>   pretty (IInd h hi d) = wrapDoc
>       (kword KwIInd <+> pretty h ArgSize <+> pretty hi ArgSize <+> pretty d ArgSize)
>       ArgSize

> import -> ElimTyRules where
>   elimTy chev (_ :<: (IMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>     return (Out, idescOp @@ [ii , x $$ A i , L $ HF "i" $ \i -> C (IMu tt i)])

> import -> Operators where
>   idescOp :
>   iboxOp :
>   imapBoxOp :
>   ielimOp :

> import -> OpCompile where
>   ("ielimOp", [iI,d,i,v,bp,p]) -> App (Var "__ielim") [d, p, i, v]
>   ("imapBox", [iI,d,x,bp,p,v]) -> App (Var "__imapBox") [d, p, v]

> import -> OpCode where
>   idescOp :: Op
>   idescOp = Op
>     { opName = "idescOp"
>     , opArity = 3
>     , opTyTel = idOpTy
>     , opRun = idOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       idOpTy = 
>        "i" :<: SET :-: \i ->
>        "d" :<: IDESC i :-: \d ->
>        "x" :<: ARR i SET :-: \x ->
>        Target SET
>       idOpRun :: [VAL] -> Either NEU VAL
>       idOpRun [ii,IDONE p,x]    = Right $ PRF p
>       idOpRun [ii,IARG aa d,x] = Right $
>          eval [.ii.aa.d.x. 
>               SIGMA (NV aa) . L $ "a" :. [.a.
>               (N (idescOp :@ [NV ii,d $# [a],NV x]))
>               ]] $ B0 :< ii :< aa :< d :< x
>       idOpRun [ii,IIND1 i d,x] = Right (TIMES (x $$ A i) (idescOp @@ [ii,d,x]))
>       idOpRun [ii,IIND h hi d,x] = 
>         Right (TIMES (PI h (L $ HF "h" (\h -> x $$ (A (hi $$ (A h)))))) 
>                      (idescOp @@ [ii,d,x]))
>       idOpRun [_,N x,_]     = Left x

>   iboxOp :: Op
>   iboxOp = Op
>     { opName = "iboxOp"
>     , opArity = 4
>     , opTyTel = iboxOpTy
>     , opRun = iboxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       iboxOpTy = 
>         "ii" :<: SET :-: \ii ->
>         "d" :<: IDESC ii :-: \d ->
>         "x" :<: ARR ii SET :-: \x ->
>         "v" :<: (idescOp @@ [ii,d,x]) :-: \v ->
>         Target $ IDESC (SIGMA ii (L $ HF "i" (\i -> x $$ A i)))
>       iboxOpRun :: [VAL] -> Either NEU VAL
>       iboxOpRun [ii,IDONE _ ,x,v] = Right (IDONE TRIVIAL)
>       iboxOpRun [ii,IARG a d,x,v] = Right $ 
>         iboxOp @@ [ii,d $$ (A (v $$ Fst)),x,v $$ Snd]
>       iboxOpRun [ii,IIND h hi d,x,v] = Right $
>         IIND h (L (HF "h" $ \hh -> PAIR (hi $$ A hh) (v $$ Fst $$ A hh))) 
>              (iboxOp @@ [ii,d,x,v $$ Snd])
>       iboxOpRun [ii,IIND1 i d,x,v] = Right $ 
>         IIND1 (PAIR i (v $$ Fst)) (iboxOp @@ [ii,d,x,v $$ Snd])
>       iboxOpRun [_,N x    ,_,_] = Left x

>   imapBoxOp :: Op
>   imapBoxOp = Op
>     { opName = "imapBoxOp"
>     , opArity = 6
>     , opTyTel = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy = 
>         "ii" :<: SET :-: \ii ->
>         "d" :<: IDESC ii :-: \d ->
>         "x" :<: ARR ii SET :-: \x ->
>         let sigiix = SIGMA ii (L (HF "i" $ \i -> x $$ A i)) in
>           "bp" :<: ARR sigiix SET :-: \bp ->
>           "p" :<: (PI sigiix (L (HF "t" $ \t -> bp $$ A t))) :-: \p ->
>           "v" :<: (idescOp @@ [ii,d,x]) :-: \v ->
>           Target $ idescOp @@ [sigiix,iboxOp @@ [ii,d,x,v],bp]
>       mapBoxOpRun :: [VAL] -> Either NEU VAL
>       mapBoxOpRun [ii,IDONE _,x,bp,p,v] = Right VOID
>       mapBoxOpRun [ii,IARG a d,x,bp,p,v] = Right $ 
>         imapBoxOp @@ [ii,d $$ (A (v $$ Fst)),x,bp,p,v $$ Snd]
>       mapBoxOpRun [ii,IIND h hi d,x,bp,p,v] = Right $ 
>         PAIR (L (HF "x" $ \x -> p $$ A (PAIR (hi $$ A x) (v $$ Fst $$ A x)))) 
>              (imapBoxOp @@ [ii,d,x,bp,p,v $$ Snd]) 
>       mapBoxOpRun [ii,IIND1 i d,x,bp,p,v] = Right $ 
>         PAIR (p $$ A (PAIR i (v $$ Fst))) (imapBoxOp @@ [ii,d,x,bp,p,v $$ Snd]) 
>       mapBoxOpRun [_,N d    ,_, _,_,_] = Left d

>   ielimOpTy :: Maybe VAL -> TEL TY
>   ielimOpTy l = 
>     "ii" :<: SET :-: \ii ->
>     "d" :<: (ARR ii (IDESC ii)) :-: \d ->
>     "i" :<: ii :-: \i ->
>     "v" :<: (IMU l ii d i) :-: \v ->
>     "bp" :<: (ARR (SIGMA ii (L (HF "i'" $ \i' -> IMU l ii d i')))
>                   SET) 
>                :-: \bp ->
>     "m" :<: 
>       (pity ("i'" :<: ii :-: \i' ->
>              "x" :<: (idescOp @@ 
>                        [ ii , d $$ A i'
>                        , L $ HF "i''" $ \i'' -> IMU l ii d i''
>                        ]) :-: \x ->
>              "hs" :<: (idescOp @@ 
>                         [ SIGMA ii (L $ HF "i" $ \i -> IMU l ii d i) 
>                         , iboxOp @@
>                              [ ii , d $$ A i'
>                              , L $ HF "i''" $ \i'' -> IMU l ii d i''
>                              , x
>                              ]
>                         , bp ]) :-: \hs ->
>              Target (bp $$ A (PAIR i' (CON x))))) :-: \m ->
>      Target (bp $$ A (PAIR i v))
>   ielimOp :: Op
>   ielimOp = Op
>     { opName = "ielimOp"
>     , opArity = 6
>     , opTyTel = ielimOpTy Nothing
>     , opRun = elimOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [ii,d,i,CON x,bp,m] = Right $ 
>         m $$ A i $$ A x 
>           $$ A (imapBoxOp @@ 
>                   [ ii , d $$ A i , L $ HF "i'" $ \i' -> IMU Nothing ii d i'
>                   , bp , L $ HF "t" $ \t -> 
>                            elimOp @@ [ii,d,t $$ Fst,t $$ Snd,bp,m] 
>                   , x
>                   ])
>       elimOpRun [_,_,_,N x, _,_] = Left x

>   imapOp = Op
>     { opName  = "imap"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = mapOpRun
>     , opSimp  = undefined 
>     } where
>         mapOpTy = 
>           "iI" :<: SET :-: \iI ->
>           "d" :<: IDESC iI :-: \d -> 
>           "a" :<: ARR iI SET :-: \a ->
>           "b" :<: ARR iI SET :-: \b ->
>           "f" :<: PI iI (L (HF "i" $ \i -> ARR (a $$ A i) (b $$ A i))) 
>                     :-: \f ->
>           "x" :<: (descOp @@ [iI, d, a]) :-: \x -> 
>           Target (descOp @@ [iI, d, b])
>
>         mapOpRun :: [VAL] -> Either NEU VAL
>         mapOpRun [iI,IDONE _,    a, b, f, x] = Right x
>         mapOpRun [iI,IARG s d, a, b, f, x] = Right $
>                 PAIR (x $$ Fst)
>                      (mapOp @@ [iI, d $$ A (x $$ Fst), a, b, f, x $$ Snd])
>         mapOpRun [iI,IIND h hi d, a, b, f, x] = Right $
>                 PAIR (L $ HF "h" $ \h -> f $$ A (hi $$ A h) 
>                                            $$ A (x $$ Fst $$ A h))
>                      (mapOp @@ [iI, d, a, b, f, x $$ Snd])
>         mapOpRun [iI,IIND1 i d,  a, b, f, x] = Right $
>                 PAIR (f $$ A i $$ A (x $$ Fst))
>                      (mapOp @@ [iI, d, a, b, f, x $$ Snd])
>         mapOpRun [iI,N d,        a, b, f, x] = Left d
> 
>         mapOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>         mapOpSimp [iI, d, a, b, f, N x] r
>           | equal (PI iI (L (HF "i" $ \i -> ARR (a $$ A i) (b $$ A i))) 
>                      :>: (f, identity)) r = pure x
>           where
>             identity = L (HF "i" (\_ -> L (HF "x" (\x -> x))))
>         mapOpSimp [iI, d, _, c, f, N (mOp :@ [_ , _, a, _, g, N x])] r
>           | mOp == mapOp = mapOpSimp args r <|> pure (mapOp :@ args)
>           where
>             comp f g = 
>                L (HF "i" $ \i -> 
>                  L (HF "x" $ \x -> f $$ A i $$ A (g $$ A i $$ A x)))
>             args = [iI, d, a, c, comp f g, N x]
>         mapOpSimp _ _ = empty

> 
