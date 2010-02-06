\section{IDesc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.IMDesc where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where
>   IMDesc   :: t -> Can t
>   IMMu     :: Labelled (Id :*: Id) t -> t -> Can t
>   IMAt     :: t -> Can t
>   IMPi     :: t -> t -> Can t
>   IMSigma  :: t -> t -> Can t
>   IMFSigma :: t -> t -> Can t
>   IMProp   :: t -> Can t
>   IMProd   :: t -> t -> Can t

> import -> CanTyRules where
>   canTy chev (Set :>: IMMu (ml :?=: (Id ii :& Id x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (IMDESC iiv) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ IMMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
>   canTy chev (IMMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>     yyv <- chev (imdescOp @@ [ ii
>                            , x $$ A i 
>                            , L $ HF "i" $ \i -> C (IMMu tt i)
>                            ] :>: y)
>     return $ Con yyv
>   canTy chev (Set :>: IMDesc ii) = 
>     (|IMDesc (chev (SET :>: ii))|)
>   canTy chev (IMDesc _I :>: IMAt i) = do
>     iiv@(i :=>: iv) <- chev (_I :>: i)
>     return $ IMAt iiv
>   canTy chev (IMDesc _I :>: IMPi s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv (IMDESC _I) :>: t)
>     return $ IMPi ssv ttv
>   canTy chev (IMDesc _I :>: IMSigma s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv (IMDESC _I) :>: t)
>     return $ IMSigma ssv ttv
>   canTy chev (IMDesc _I :>: IMFSigma e b) = do
>     eev@(e :=>: ev) <- chev (enumU :>: e)
>     bbv@(b :=>: bv) <- chev (branchesOp @@ [ ev
>                                            , L (K (IMDESC _I))] :>: b)
>     return $ IMFSigma eev bbv
>   canTy chev (IMDesc _I :>: IMProp q) = do
>     qqv@(q :=>: qv) <- chev (PROP :>: q)
>     return $ IMProp qqv
>   canTy chev (IMDesc _I :>: IMProd x y) = do
>     xxv@(x :=>: xv) <- chev (IMDESC _I :>: x)
>     yyv@(y :=>: yv) <- chev (IMDESC _I :>: y)
>     return $ IMProd xxv yyv

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where
>   pattern IMDESC i = C (IMDesc i)
>   pattern IMMU l ii x i = C (IMMu (l :?=: (Id ii :& Id x)) i) 
>   pattern IMAT i = C (IMAt i)
>   pattern IMPI s t = C (IMPi s t)
>   pattern IMSIGMA s t = C (IMSigma s t)
>   pattern IMFSIGMA s t = C (IMFSigma s t)
>   pattern IMPROP p = C (IMProp p)
>   pattern IMPROD x y = C (IMProd x y)

> import -> CanDisplayPats where
>   pattern DIMDESC i = DC (IMDesc i)
>   pattern DIMMU l ii x i = DC (IMMu (l :?=: (Id ii :& Id x)) i) 
>   pattern DIMAT i = DC (IMAt i)
>   pattern DIMPI s t = DC (IMPi s t)
>   pattern DIMSIGMA s t = DC (IMSigma s t)
>   pattern DIMFSIGMA s t = DC (IMFSigma s t)
>   pattern DIMPROP p = DC (IMProp p)
>   pattern DIMPROD x y = DC (IMProd x y)

> import -> CanPretty where
>   pretty (IMDesc ii) = wrapDoc (kword KwIMDesc <+> pretty ii ArgSize) ArgSize
>   pretty (IMMu (Just l   :?=: _) i)  = wrapDoc
>       (pretty l ArgSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMMu (Nothing  :?=: (Id ii :& Id d)) i)  = wrapDoc
>       (kword KwIMMu <+> pretty ii ArgSize <+> pretty d ArgSize <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMAt i) = wrapDoc
>       (kword KwIMAt <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMPi s t) = wrapDoc
>       (kword KwIMPi <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IMSigma s t) = wrapDoc
>       (kword KwIMSigma <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IMFSigma s t) = wrapDoc
>       (kword KwIMFSigma <+> pretty s ArgSize <+> pretty t ArgSize)
>       ArgSize
>   pretty (IMProp i) = wrapDoc
>       (kword KwIMProp <+> pretty i ArgSize)
>       ArgSize
>   pretty (IMProd x y) = wrapDoc
>       (kword KwIMProd <+> pretty x ArgSize <+> pretty y ArgSize)
>       ArgSize

> import -> CanTraverse where
>   traverse f (IMDesc i)     = (|IMDesc (f i)|)
>   traverse f (IMMu l i)     = (|IMMu (traverse f l) (f i)|)
>   traverse f (IMAt i)       = (|IMAt (f i)|)
>   traverse f (IMPi s t)     = (|IMPi (f s) (f t)|)
>   traverse f (IMSigma s t)  = (|IMSigma (f s) (f t)|)
>   traverse f (IMFSigma s t) = (|IMFSigma (f s) (f t)|)
>   traverse f (IMProp p)     = (|IMProp (f p)|)
>   traverse f (IMProd x y)   = (|IMProd (f x) (f y)|)

> import -> CanHalfZip where
>   halfZip (IMDesc i0) (IMDesc i1) = (|(IMDesc (i0,i1))|)
>   halfZip (IMMu l0 i0) (IMMu l1 i1) = (|(\p -> IMMu p (i0,i1)) (halfZip l0 l1)|)
>   halfZip (IMAt i0) (IMAt i1) = (|(IMAt (i0,i1))|)
>   halfZip (IMPi s0 t0) (IMPi s1 t1) = (|(IMPi (s0,s1) (t0,t1))|)
>   halfZip (IMSigma s0 t0) (IMSigma s1 t1) = (|(IMSigma (s0,s1) (t0,t1))|)
>   halfZip (IMFSigma s0 t0) (IMFSigma s1 t1) = (|(IMFSigma (s0,s1) (t0,t1))|)
>   halfZip (IMProp p0) (IMProp p1) = (|(IMProp (p0,p1))|)
>   halfZip (IMProd s0 t0) (IMProd s1 t1) = (|(IMProd (s0,s1) (t0,t1))|)

\subsection{Plugging Eliminators in}

> import -> ElimTyRules where
>   elimTy chev (_ :<: (IMMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>     return (Out, imdescOp @@ [ii , x $$ A i , L $ HF "i" $ \i -> C (IMMu tt i)])

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

\subsection{Plugging Operators in}

> import -> Operators where
>   imdescOp :

> import -> OpCompile where
>  -- ("imfold", [iI,d,i,v,bp,p]) -> App (Var "__imfold") [d, p, i, v]
>  -- ("immapBox", [iI,d,x,bp,p,v]) -> App (Var "__immapBox") [d, p, v]

> import -> OpCode where
>   imdescOp :: Op
>   imdescOp = Op
>     { opName = "imdesc"
>     , opArity = 3
>     , opTyTel = idOpTy
>     , opRun = idOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       idOpTy = 
>        "I" :<: SET :-: \iI ->
>        "d" :<: IMDESC iI :-: \d ->
>        "X" :<: ARR iI SET :-: \x ->
>        Target SET

>       idOpRun :: [VAL] -> Either NEU VAL
>       idOpRun [_I, IMAT i          , _P] = Right $
>           _P $$ A i
>       idOpRun [_I, IMPI _S _T      , _P] = Right $
>           PI _S (L . HF "s" $ \s ->
>                  imdescOp @@ [ _I
>                              , _T $$ A s
>                              , _P ])
>       idOpRun [_I, IMSIGMA _S _T   , _P] = Right $
>           SIGMA _S (L . HF "s" $ \s ->
>                     imdescOp @@ [ _I
>                                 , _T $$ A s
>                                 , _P ])
>       idOpRun [_I, IMFSIGMA _S _T  , _P] = Right $
>           SIGMA (ENUMT _S) (L . HF "s" $ \s ->
>                             imdescOp @@ [ _I
>                                         , switchOp @@ [ _S
>                                                       , s
>                                                       , L (K (IMDESC _I))
>                                                       , _T]
>                                         , _P])
>       idOpRun [_I, IMPROP p        , _P] = Right $
>           PRF p
>       idOpRun [_I, IMPROD _D _D'   , _P] = Right $
>           TIMES  (imdescOp @@ [ _I, _D, _P ])
>                  (imdescOp @@ [ _I, _D', _P ])
>       idOpRun [_,N x               ,_]   = Left x

>   imcurryDOp :: Op
>   imcurryDOp = Op
>     { opName = "imcurryD"
>     , opArity = 4
>     , opTyTel = imcurryDOpTy
>     , opRun = imcurryDOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       imcurryDOpTy =
>           "I" :<: SET                               :-: \ _I ->
>           "D" :<: IMDESC _I                         :-: \ _D ->
>           "P" :<: ARR _I SET                        :-: \ _P ->
>           "R" :<: ARR (imdescOp @@ [_I,_D,_P]) SET  :-: \ _R ->
>           Target SET
>       imcurryDOpRun :: [VAL] -> Either NEU VAL
>       imcurryDOpRun [_I, N x, _P, _R] = Left x
>       imcurryDOpRun [_I, IMAT i, _P, _R] = Right $
>           PI (_P $$ A i) (L . HF "x" $ \x -> _R $$ A x)
>       imcurryDOpRun [_I, IMPI _S _T, _P, _R] = Right $
>           PI _S (L . HF "s" $ \s ->
>                  imcurryDOp @@ [ _I
>                                , _T $$ A s
>                                , _P
>                                , L . HF "d" $ \d -> _R $$ A s $$ A d ])
>       imcurryDOpRun [_I, IMSIGMA _S _T, _P, _R] = Right $
>           PI _S (L . HF "s" $ \s ->
>                  imcurryDOp @@ [ _I
>                                , _T $$ A s
>                                , _P
>                                , L . HF "d" $ \d -> _R $$ A (PAIR s d)])
>       imcurryDOpRun [_I, IMFSIGMA _E _B, _P, _R] = Right $
>           branchesOp @@ [ _E
>                         , L . HF "e" $ \e ->
>                           imcurryDOp @@ [ _I
>                                         , switchOp @@ [ _E
>                                                       , e
>                                                       , L (K (IMDESC _I))
>                                                       , _B ]
>                                         , _P
>                                         , L . HF "d" $ \d -> _R $$ A (PAIR e d)]]
>       imcurryDOpRun [_I, IMPROP q, _P, _R] = Right $
>           PI (PRF q) (L . HF "x" $ \x -> _R $$ A x)
>       imcurryDOpRun [_I, IMPROD _D _D', _P, _R] = Right $
>           imcurryDOp @@ [_I, _D, _P, L . HF "d" $ \d ->
>            imcurryDOp @@ [_I, _D', _P, L . HF "d'" $ \d' -> _R $$ A (PAIR d d')]]

>   imboxOp :: Op
>   imboxOp = Op
>     { opName = "imbox"
>     , opArity = 4
>     , opTyTel = imboxOpTy
>     , opRun = imboxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       imboxOpTy = 
>         "I" :<: SET                     :-: \ _I ->
>         "D" :<: IMDESC _I               :-: \ _D ->
>         "P" :<: ARR _I SET              :-: \ _P ->
>         "v" :<: imdescOp @@ [_I,_D,_P]  :-: \v ->
>         Target $ IDESC (SIGMA _I (L . HF "i" $ \i -> _P $$ A i))

>       imboxOpRun :: [VAL] -> Either NEU VAL
>       imboxOpRun [_,N x    ,_,_] = Left x
>       imboxOpRun [_I, IMAT i, _P, v] = Right $ 
>           IMAT (PAIR i v)
>       imboxOpRun [_I, IMPI _S _T, _P, f] = Right $
>           IMPI _S (L . HF "s" $ \s ->
>                    imboxOp @@ [_I, _T $$ A s, _P, f $$ A s])
>       imboxOpRun [_I, IMSIGMA _S _T, _P, sd] = Right $
>           let s = sd $$ Fst
>               d = sd $$ Snd in
>           imboxOp @@ [_I, _T $$ A s, _P, d]
>       imboxOpRun [_I, IMFSIGMA _E _B, _P, ed] = Right $
>            let e = ed $$ Fst
>                d = ed $$ Snd in
>            imboxOp @@ [_I
>                       , switchOp @@ [ _E
>                                     , e
>                                     , L (K (IMDESC _I))
>                                     , _B ]
>                       , _P 
>                       , d ]
>       imboxOpRun [_I, IMPROP _Q, _P, q] = Right $
>           IMPROP TRIVIAL
>       imboxOpRun [_I, IMPROD _D _D', _P, dd'] = Right $
>           let d = dd' $$ Fst
>               d' = dd' $$ Snd in
>           IMPROD  (imboxOp @@ [_I, _D, _P, d])
>                   (imboxOp @@ [_I, _D', _P, d'])
           
>   imelimOp :: Op
>   imelimOp = Op
>     { opName = "iinductionC"
>     , opArity = 6
>     , opTyTel = imelimOpTy 
>     , opRun = imelimOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       imelimOpTy = 
>           "I" :<: SET                       :-: \ _I ->
>           "D" :<: ARR _I (IMDESC _I)        :-: \ _D ->
>           "i" :<: _I                        :-: \ i ->
>           "v" :<: IMMU Nothing _I _D i      :-: \ v ->
>           "P" :<: ARR  (SIGMA _I (L . HF "i'" $ \i' -> IMMU Nothing _I _D i'))
>                        SET                  :-: \ _P ->
>           "m" :<: PI _I (L . HF "i'" $ \i' ->
>                          imcurryDOp @@ [ _I
>                                        , _D $$ A i'
>                                        , L . HF "i" $ \i -> IMMU Nothing _I _D i
>                                        , L . HF "xs" $ \xs ->
>                                          imcurryDOp @@ [ _I
>                                                        , imboxOp @@ [ _I
>                                                                     , _D $$ A i'
>                                                                     , L . HF "i" $ \i -> IMMU Nothing _I _D i
>                                                                     , xs ]
>                                                        , _P 
>                                                        , L (K (_P $$ A (PAIR i' (CON xs))))]]) :-: \m ->
>           Target $ _P $$ A (PAIR i v)
>       imelimOpRun :: [VAL] -> Either NEU VAL
>       imelimOpRun [_,_,_,N x, _,_] = Left x
>       imelimOpRun [ii,d,i,CON x,bp,m] = Right $ undefined



\subsection{Plugging Axioms in}

> import -> Axioms where

> import -> AxCode where

\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where
>   coerce (IMMu (Just (l0,l1) :?=: 
>                (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) = 
>     let ql  = CON $ q $$ Fst
>         qiI = CON $ q $$ Snd $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Snd $$ Fst
>         (typ :>: vap) = 
>           laty ("I" :<: SET :-: \iI ->
>                 "d" :<: ARR iI (IMDESC iI) :-: \d ->
>                 "i" :<: iI :-: \i ->
>                 "l" :<: ARR iI SET :-: \l ->
>                 Target (SET :>: 
>                           idescOp @@ [ iI , d $$ A i
>                                      , L $ HF "i" $ IMMU (|l|) iI d
>                                      ]))
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [iI0, d0 $$ A i0, L $ HF "i" $ IMMU (|l0|) iI0 d0] 
>              , idescOp @@ [iI1, d1 $$ A i1, L $ HF "i" $ IMMU (|l1|) iI1 d1] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>                                $$ A l0 $$ A l1 $$ A ql
>              , x ]
>   coerce (IMMu (Nothing :?=: (Id (iI0,iI1) :& Id (d0,d1))) (i0,i1)) q (CON x) =
>     let qiI = CON $ q $$ Fst
>         qi  = CON $ q $$ Snd $$ Snd
>         qd = CON $ q $$ Snd $$ Fst
>         (typ :>: vap) = 
>           laty ("I" :<: SET :-: \iI ->
>                 "d" :<: ARR iI (IMDESC iI) :-: \d ->
>                 "i" :<: iI :-: \i ->
>                 Target (SET :>: 
>                           (idescOp @@ [ iI , d $$ A i
>                                       , L $ HF "i" $ IMMU Nothing iI d
>                                       ]))) 
>     in Right . CON $ 
>       coe @@ [ idescOp @@ [ iI0 , d0 $$ A i0 , L $ HF "i" $ IMMU Nothing iI0 d0 ] 
>              , idescOp @@ [ iI1 , d1 $$ A i1 , L $ HF "i" $ IMMU Nothing iI1 d1 ] 
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A iI0 $$ A iI1 $$ A qiI
>                                $$ A d0 $$ A d1 $$ A qd
>                                $$ A i0 $$ A i1 $$ A qi
>              , x ]


\subsection{Extending the quotient}

> import -> QuotientDefinitions where

\subsection{Extending the Display Language}

> import -> ElaborateRules where
>   elaborate True (SET :>: DIMMU Nothing iI d i) = do
>       GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>       let fr = nom := FAKE :<: ty
>       xs <- getBoys
>       guard (not (null xs))
>       let lt = N (P fr $:$ (map (\x -> A (N (P x))) (init xs)))
>       let lv = evTm lt
>       (iI :=>: iIv) <- elaborate False (SET :>: iI)
>       (d :=>: dv) <- elaborate False (ARR iIv (IMDESC iIv) :>: d)
>       (i :=>: iv) <- elaborate False (iIv :>: i)
>       lastIsIndex <- withNSupply (equal (SET :>: (iv,N (P (last xs)))))
>       guard lastIsIndex
>       -- should check i doesn't appear in d (fairly safe it's not in iI :))
>       return (IMMU (Just lt) iI d i :=>: IMMU (Just lv) iIv dv iv)
 
> import -> DistillRules where
>     distill es (SET :>: tm@(C (IMMu l i)))
>       | Just name <- extractLabelName l = do
>           mtm <- lookupName name
>           case mtm of
>               Nothing  -> distill es (SET :>: C (IMMu (dropLabel l) i))
>               Just _   -> do
>                   cc <- canTy (distill es) (Set :>: IMMu l i)
>                   return ((DC $ fmap termOf cc) :=>: evTm tm)

> import -> InDTmConstructors where

> import -> InDTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where

\subsection{Extending the Mangler}

> import -> DMangleRules where
