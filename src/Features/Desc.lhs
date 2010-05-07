\section{A universe of descriptions: |Desc|}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Desc where

%endif


\subsection{Plugging Canonical terms in}

> import -> CanConstructors where
>   Mu     :: Labelled Id t -> Can t

> import -> CanTyRules where
>   canTy chev (Set :>: Mu (ml :?=: Id x))     = do
>     mlv <- traverse (chev . (SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (desc :>: x)
>     return $ Mu (mlv :?=: Id xxv)
>   canTy chev (t@(Mu (_ :?=: Id x)) :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [x, C t] :>: y)
>     return $ Con yyv

> import -> CanCompile where

> import -> CanEtaExpand where

> import -> CanPats where
>   pattern IDN     = ZE
>   pattern CONSTN  = SU ZE
>   pattern SUMN    = SU (SU ZE)
>   pattern PRODN   = SU (SU (SU ZE))
>   pattern SIGMAN  = SU (SU (SU (SU ZE)))
>   pattern PIN     = SU (SU (SU (SU (SU ZE))))

>   pattern MU l x      = C (Mu (l :?=: Id x))
>   pattern IDD         = CON (PAIR IDN     VOID)
>   pattern CONSTD x    = CON (PAIR CONSTN  (PAIR x VOID))
>   pattern SUMD e b    = CON (PAIR SUMN    (PAIR e (PAIR b VOID)))
>   pattern PRODD d d'  = CON (PAIR PRODN   (PAIR d (PAIR d' VOID)))
>   pattern SIGMAD s t  = CON (PAIR SIGMAN  (PAIR s (PAIR t VOID)))
>   pattern PID s t     = CON (PAIR PIN     (PAIR s (PAIR t VOID)))

> import -> CanDisplayPats where
>   pattern DMU l x      = DC (Mu (l :?=: Id x))
>   pattern DIDD         = DCON (DPAIR  DZE 
>                                       DVOID)
>   pattern DCONSTD x    = DCON (DPAIR  (DSU DZE)
>                                       (DPAIR x DVOID))
>   pattern DSUMD e b    = DCON (DPAIR  (DSU (DSU DZE))
>                                       (DPAIR e (DPAIR b DVOID)))
>   pattern DPRODD d d'  = DCON (DPAIR  (DSU (DSU (DSU DZE)))
>                                       (DPAIR d (DPAIR d' DVOID)))
>   pattern DSIGMAD s t  = DCON (DPAIR  (DSU (DSU (DSU (DSU DZE))))
>                                       (DPAIR s (DPAIR t DVOID)))
>   pattern DPID s t     = DCON (DPAIR  (DSU (DSU (DSU (DSU (DSU DZE)))))
>                                       (DPAIR s (DPAIR t DVOID)))

> import -> CanPretty where
>   pretty (Mu (Just l   :?=: _))     = pretty l
>   pretty (Mu (Nothing  :?=: Id t))  = wrapDoc
>       (kword KwMu <+> pretty t ArgSize)
>       ArgSize

> import -> CanTraverse where
>   traverse f (Mu l) = (|Mu (traverse f l)|)

> import -> CanHalfZip where
>   halfZip (Mu t0) (Mu t1) = (| Mu (halfZip t0 t1) |)

\subsection{Plugging Eliminators in}

> import -> ElimTyRules where
>   elimTy chev (_ :<: t@(Mu (_ :?=: Id d))) Out = return (Out, descOp @@ [d , C t])

> import -> ElimComputation where

> import -> ElimCompile where

> import -> ElimTraverse where

> import -> ElimPretty where

\subsection{Plugging Operators in}

> import -> Operators where
>   descOp :
>   boxOp :
>   mapBoxOp :
>   mapOp :
>   inductionOp :
>   branchesDOp :
>   switchDOp :

> import -> OpCompile where
>   ("induction", [d,v,bp,p]) -> App (Var "__induction") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   ("switchD", [e,b,x]) -> App (Var "__switch") [x, b]


> import -> OpCode where

>   type DescDispatchTable = (VAL, 
>                         VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL)


The |mkLazyDescDef| function lazily eliminates a desc value (i.e. |d| such that
|desc :>: CON d|. If the tag is canonical, it calls the corresponding case in
the dispatch table with the relevant arguments; otherwise, it cannot compute,
so it returns a term on the |Left|.

>   mkLazyDescDef :: VAL -> DescDispatchTable -> Either NEU VAL
>   mkLazyDescDef arg (idCase, constCase, sumCase, prodCase, sigmaCase, piCase) =
>       let args = arg $$ Snd in
>         case arg $$ Fst of      
>           IDN     -> Right $ idCase
>           CONSTN  -> Right $ constCase  (args $$ Fst)
>           SUMN    -> Right $ sumCase    (args $$ Fst) (args $$ Snd $$ Fst)
>           PRODN   -> Right $ prodCase   (args $$ Fst) (args $$ Snd $$ Fst)
>           SIGMAN  -> Right $ sigmaCase  (args $$ Fst) (args $$ Snd $$ Fst)

>           PIN     -> Right $ piCase     (args $$ Fst) (args $$ Snd $$ Fst)
>           N t     -> Left t
>           _       -> error "mkLazyDescDef: invalid constructor!"

>   descOp :: Op
>   descOp = Op
>     { opName = "desc"
>     , opArity = 2
>     , opTyTel = dOpTy
>     , opRun = dOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       dOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         Target SET
>       dOpRun :: [VAL] -> Either NEU VAL
>       dOpRun [CON arg, _X]  = mkLazyDescDef arg (idCase _X, 
>                                                  constCase _X, 
>                                                  sumCase _X, 
>                                                  prodCase _X, 
>                                                  sigmaCase _X, 
>                                                  piCase _X)
>       dOpRun [N _D, _]      = Left _D
>           
>       idCase _X          = _X
>       constCase _X _Z    = _Z
>       sumCase _X _E _B   = SIGMA (ENUMT _E) .
>                                  L $ HF "x" $ \x ->
>                                 descOp @@ [ switchDOp @@ [_E, _B, x]  , _X]
>       prodCase _X _D _D' = TIMES  (descOp @@ [ _D , _X ])
>                                   (descOp @@ [ _D', _X ])
>       sigmaCase _X _S _T = SIGMA  _S . 
>                                   L $ HF "s" $ \s ->
>                                   descOp @@ [ _T $$ A s, _X ]
>       piCase _X _S _T    = PI  _S . 
>                                L $ HF "s" $ \s ->
>                                descOp @@ [ _T $$ A s, _X ]


>   boxOp :: Op
>   boxOp = Op
>     { opName = "box"
>     , opArity = 4
>     , opTyTel = boxOpTy
>     , opRun = boxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       boxOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         "P" :<: ARR xX SET :-: \pP ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>         Target SET
>       boxOpRun :: [VAL] -> Either NEU VAL
>       boxOpRun [CON arg, _X, _P, x]  = mkLazyDescDef arg (idCase _X _P x, 
>                                                       constCase _X _P x, 
>                                                       sumCase _X _P x, 
>                                                       prodCase _X _P x, 
>                                                       sigmaCase _X _P x, 
>                                                       piCase _X _P x)
>       boxOpRun [N x,           _,_,_] = Left x
>       idCase _X _P x = _P $$ A x
>       constCase _X _P x _Z = _Z
>       sumCase _X _P ab _E _B = 
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in boxOp @@ [switchDOp @@ [_E, _B, a], _X, _P, b]
>       prodCase _X _P dd' _D _D' = 
>           let d  = dd' $$ Fst
>               d' = dd' $$ Snd 
>           in TIMES  (boxOp @@ [_D, _X, _P, d])
>                     (boxOp @@ [_D', _X, _P, d'])
>       sigmaCase _X _P ab _S _T = 
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in boxOp @@ [_T $$ A a, _X, _P, b]
>       piCase _X _P f _S _T =
>           PI  _S . 
>               L $ HF "s" $ \s -> 
>               boxOp @@ [_T $$ A s, _X, _P, f $$ A s]


>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBox"
>     , opArity = 5
>     , opTyTel = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy =  
>         "D" :<: desc :-: \ dD ->
>         "X" :<: SET :-: \ xX ->
>         "P" :<: ARR xX SET :-: \ pP ->
>         "p" :<: (pity $ "x" :<: xX :-: \ x -> Target $ pP $$ A x) :-: \ _ ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>          Target (boxOp @@ [dD,xX,pP,v])
>       mapBoxOpRun :: [VAL] -> Either NEU VAL
>       mapBoxOpRun [CON arg, _X, _P, _R, x]  = mkLazyDescDef arg (idCase _X _P _R x, 
>                                                              constCase _X _P _R x, 
>                                                              sumCase _X _P _R x, 
>                                                              prodCase _X _P _R x, 
>                                                              sigmaCase _X _P _R x, 
>                                                              piCase _X _P _R x)
>       mapBoxOpRun [N x,     _, _,_,_]       = Left x
>
>       idCase _X _P _R v = _R $$ A v
>       constCase _X _P _R z _Z = z
>       sumCase _X _P _R ab _E _B =
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in mapBoxOp @@ [switchDOp @@ [_E, _B, a], _X, _P, _R, b]
>       prodCase _X _P _R dd' _D _D' = 
>           let d  = dd' $$ Fst
>               d' = dd' $$ Snd 
>           in PAIR  (mapBoxOp @@ [_D,  _X, _P, _R, d])
>                    (mapBoxOp @@ [_D', _X, _P, _R, d'])
>       sigmaCase _X _P _R ab _S _T =
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in mapBoxOp @@ [_T $$ A a, _X, _P, _R, b]
>       piCase _X _P _R f _S _T =
>           L . HF "s" $ \s ->
>           mapBoxOp @@ [_T $$ A s, _X, _P, _R, f $$ A s]


>   mapOp = Op
>     { opName  = "map"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = mapOpRun
>     , opSimp  = \_ _ -> empty
>     } where
>         mapOpTy = 
>           "dD" :<: desc :-: \dD -> 
>           "xX" :<: SET :-: \xX ->
>           "yY" :<: SET :-: \yY ->
>           "f" :<: ARR xX yY :-: \f ->
>           "v" :<: (descOp @@ [dD, xX]) :-: \v -> 
>           Target (descOp @@ [dD, yY])
>         mapOpRun :: [VAL] -> Either NEU VAL
>         mapOpRun [CON arg, _X, _Y, f, v]  = mkLazyDescDef arg (idCase _X _Y f v, 
>                                                            constCase _X _Y f v, 
>                                                            sumCase _X _Y f v, 
>                                                            prodCase _X _Y f v, 
>                                                            sigmaCase _X _Y f v, 
>                                                            piCase _X _Y f v)
>         mapOpRun [N d,     a, b, f, x] = Left d
>
>         idCase _X _Y sig x = sig $$ A x
>         constCase _X _Y sig z _Z = z
>         sumCase _X _Y sig ab _E _B = 
>             let a = ab $$ Fst
>                 b = ab $$ Snd
>             in PAIR a (mapOp @@ [ switchDOp @@ [_E, _B, a], _X, _Y, sig, b])
>         prodCase _X _Y sig dd' _D _D' = 
>             let d  = dd' $$ Fst
>                 d' = dd' $$ Snd 
>             in PAIR  (mapOp @@ [_D,  _X, _Y, sig, d])
>                      (mapOp @@ [_D', _X, _Y, sig, d'])
>         sigmaCase _X _Y sig ab _S _T = 
>             let a = ab $$ Fst
>                 b = ab $$ Snd
>             in PAIR a (mapOp @@ [_T $$ A a, _X, _Y, sig, b])
>         piCase _X _Y sig f _S _T =
>             L . HF "s" $ \s ->
>             mapOp @@ [_T $$ A s, _X, _Y, sig, f $$ A s]


>   inductionOpMethodType = L . HF "d" $ \d ->
>                      L . HF "P" $ \_P ->
>                      PI (descOp @@ [d, MU Nothing d])
>                         (L . HF "x" $ \x ->
>                          ARR (boxOp @@ [d, MU Nothing d, _P, x])
>                              (_P $$ A (CON x)))

>   inductionOpLabMethodType = L . HF "l" $ \l ->
>                         L . HF "d" $ \d ->
>                         L . HF "P" $ \_P ->
>                         PI (descOp @@ [d, MU (Just l) d])
>                            (L . HF "x" $ \x ->
>                             ARR (boxOp @@ [d, MU (Just l) d, _P, x])
>                                 (_P $$ A (CON x)))

>   inductionOp :: Op
>   inductionOp = Op
>     { opName = "induction"
>     , opArity = 4
>     , opTyTel = inductionOpTy
>     , opRun = inductionOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       inductionOpTy = 
>         "D" :<: desc :-: \dD ->
>         "v" :<: MU Nothing dD :-: \v ->
>         "P" :<: (ARR (MU Nothing dD) SET) :-: \pP ->
>         "p" :<: (inductionOpMethodType $$ A dD $$ A pP) :-: \p ->
>         Target (pP $$ A v)
>       inductionOpRun :: [VAL] -> Either NEU VAL
>       inductionOpRun [dD, CON v, pP, p] = Right $ 
>         p $$ A v $$ A (mapBoxOp @@ [ dD , MU Nothing dD , pP
>                                    , L $ HF "w" $ \w -> 
>                                        inductionOp @@ [ dD , w , pP , p ]
>                                    , v]) 
>       inductionOpRun [_, N x, _,_] = Left x

>   branchesDOp = Op 
>     { opName   = "branchesD"
>     , opArity  = 1
>     , opTyTel  = bOpTy
>     , opRun    = bOpRun
>     , opSimp   = \_ _ -> empty
>     } where
>         bOpTy = "e" :<: enumU :-: \e ->
>                 Target SET
>         bOpRun :: [VAL] -> Either NEU VAL
>         bOpRun [CON arg] = mkLazyEnumDef arg (nilECase, 
>                                               consECase)
>         bOpRun [N e] = Left e
>
>         nilECase       = UNIT
>         consECase t e' = TIMES desc (branchesDOp @@ [e'])



>   switchDOp = Op
>     { opName = "switchD"
>     , opArity = 3
>     , opTyTel = sOpTy
>     , opRun = sOpRun
>     , opSimp = \_ _ -> empty
>     } where
>         sOpTy = 
>           "e" :<: enumU :-: \e ->
>           "b" :<: (branchesOp @@ [e , L (K desc) ]) :-: \b ->
>           "x" :<: ENUMT e :-: \x ->
>           Target desc
>         sOpRun :: [VAL] -> Either NEU VAL
>         sOpRun [_      , _ , N n] = Left n
>         sOpRun [CON arg, ps, n] = mkLazyEnumDef arg (error "switchDOp: NilE barfs me.", 
>                                                      consECase n ps)

%if False

>         sOpRun vs = error ("Desc.SwitchD.sOpRun: couldn't handle " ++ show vs)

%endif

>
>         consECase :: VAL -> VAL -> VAL -> VAL -> VAL
>         consECase ZE     ps t e' = ps $$ Fst
>         consECase (SU n) ps t e' = switchDOp @@ [ e'
>                                                 , ps $$ Snd
>                                                 , n ]

\subsection{Plugging Axioms in}

> import -> Axioms where

> import -> AxCode where

\subsection{Extending the type-checker}

> import -> Check where

\subsection{Extending the equality}

> import -> OpRunEqGreen where

> import -> Coerce where
>   coerce (Mu (Just (l0,l1) :?=: Id (d0,d1))) q (CON x) =
>     let (typ :>: vap) = laty ("d" :<: desc :-: \d ->
>                               "l" :<: SET :-: \l ->
>                               Target (SET :>: descOp @@ [d,MU (Just l) d])) 
>     in Right . CON $ 
>       coe @@ [ descOp @@ [ d0 , MU (Just l0) d0 ] 
>              , descOp @@ [ d1 , MU (Just l1) d1 ]
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A d0 $$ A d1 $$ A (CON $ q $$ Snd)
>                                $$ A l0 $$ A l1 $$ A (CON $ q $$ Fst)
>              , x ]
>   coerce (Mu (Nothing :?=: Id (d0,d1))) q (CON x) =
>     let (typ :>: vap) = laty ("d" :<: desc :-: \d ->
>                               Target (SET :>: descOp @@ [d,MU Nothing d]))  
>     in Right . CON $ 
>       coe @@ [ descOp @@ [ d0 , MU Nothing d0 ] 
>              , descOp @@ [ d1 , MU Nothing d1 ]
>              , CON $ pval refl $$ A typ $$ A vap $$ Out 
>                                $$ A d0 $$ A d1 $$ A (CON q)
>              , x ]

\subsection{Extending the quotient}

> import -> QuotientDefinitions where

\subsection{Extending the Display Language}

> import -> MakeElabRules where
>     -- Could add rules for named constructors
>     makeElab' loc (MU l d :>: DVOID) = 
>         makeElab' loc (MU l d :>: DCON (DPAIR DZE DVOID))
>     makeElab' loc (MU l d :>: DPAIR s t) =
>         makeElab' loc (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))
>     makeElab' loc (SET :>: DMU Nothing d) = do
>         lt :=>: lv <- EFake True Bale
>         dt :=>: dv <- subElab loc (desc :>: d)
>         return $ MU (Just (N lt)) dt :=>: MU (Just lv) dv
 
>     makeElab' loc (PI (MU l d) t :>: DCON f) = do
>         d'  :=>: _    <- eQuote d
>         t'  :=>: _    <- eQuote t
>         tm  :=>: tmv  <- subElab loc $ case l of
>             Nothing  -> inductionOpMethodType $$ A d $$ A t :>: f
>             Just l   -> inductionOpLabMethodType $$ A l $$ A d $$ A t :>: f
>         x <- eLambda (fortran t)
>         return $ N (  inductionOp :@  [d',  NP x, t',  tm   ])
>                :=>:   inductionOp @@  [d,   NP x, t,   tmv  ]


> import -> DistillRules where
>     distill _ (MU _ _ :>: CON (PAIR ZE VOID)) =
>         return (DVOID :=>: CON (PAIR ZE VOID))
>     distill es (C ty@(Mu _) :>: C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID))))) = do
>         Con (DPAIR _ (DPAIR s (DPAIR t _)) :=>: v) <- canTy (distill es) (ty :>: c)
>         return ((DPAIR s t) :=>: CON v)

If a label is not in scope, we remove it, so the definition appears at the
appropriate place when the proof state is printed.

>     distill es (SET :>: tm@(C (Mu ltm))) 
>       | Just name <- extractLabelName ltm = do
>           mtm <- lookupName name
>           case mtm of
>               Nothing  -> distill es (SET :>: C (Mu (dropLabel ltm)))
>               Just _   -> do
>                   cc <- canTy (distill es) (Set :>: Mu ltm)
>                   return ((DC $ fmap termOf cc) :=>: evTm tm)

> import -> InDTmConstructors where

> import -> InDTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
>   ("Desc", descREF) :
>   ("DescD", descDREF) :

\subsection{Bootstrapping}

> import -> BootstrapDesc where
>   inDesc :: VAL
>   inDesc = SIGMAD  (ENUMT constructors) 
>                    (L $ HF "c" $ \c -> 
>                     switchDOp @@ [ constructors , cases , c ])
>       where constructors = (CONSE (TAG "idD")
>                            (CONSE (TAG "constD")
>                            (CONSE (TAG "sumD")
>                            (CONSE (TAG "prodD")
>                            (CONSE (TAG "sigmaD")
>                            (CONSE (TAG "piD")
>                             NILE))))))
>             cases = (PAIR (CONSTD UNIT) 
>                     (PAIR (SIGMAD SET (L $ K $ CONSTD UNIT))
>                     (PAIR (SIGMAD enumU (L $ HF "E" $ \_E ->
>                                         (SIGMAD (branchesDOp @@ [_E]) 
>                                                 (L $ K (CONSTD UNIT)))))
>                     (PAIR (PRODD IDD (PRODD IDD (CONSTD UNIT)))
>                     (PAIR (SIGMAD SET (L $ HF "S" $ \_S -> 
>                                       (PRODD (PID _S (L $ K IDD)) 
>                                              (CONSTD UNIT))))
>                     (PAIR (SIGMAD SET (L $ HF "S" $ \_S -> 
>                                       (PRODD (PID _S (L $ K IDD)) 
>                                              (CONSTD UNIT))))
>                      VOID))))))
>   descFakeREF :: REF
>   descFakeREF = [("Primitive", 0), ("Desc", 0)] := (FAKE :<: SET)
>   desc :: VAL
>   desc = MU (Just (N (P descFakeREF))) inDesc
>
>   descREF :: REF
>   descREF = [("Primitive", 0), ("Desc", 0)] := (DEFN desc :<: SET)
>
>   descDREF :: REF
>   descDREF = [("Primitive", 0), ("DescD", 0)] := (DEFN inDesc :<: desc)
