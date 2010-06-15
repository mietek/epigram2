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
>       AppSize

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
>   ("branchesD", _) -> Ignore


> import -> OpCode where

>   type DescDispatchTable = (VAL, 
>                         VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL,
>                         VAL -> VAL -> VAL)


The |mkLazyDescDef| function lazily eliminates a desc value (i.e. |d| such that
|desc :>: CON d|. If the tag is canonical, it calls the corresponding case in
the dispatch table with the relevant arguments; otherwise, it cannot compute,
so it returns a term on the |Left|. Note that finite sums are handled using the
case for sigma.

>   mkLazyDescDef :: VAL -> DescDispatchTable -> Either NEU VAL
>   mkLazyDescDef arg (idCase, constCase, prodCase, sigmaCase, piCase) =
>       let args = arg $$ Snd in
>         case arg $$ Fst of      
>           IDN     -> Right $ idCase
>           CONSTN  -> Right $ constCase  (args $$ Fst)
>           SUMN    -> Right $ sigmaCase  (ENUMT (args $$ Fst)) (args $$ Snd $$ Fst)
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
>     , opRun = {- dOpRun -} runOpTree $ oData
>         [ {-ID-} oTup $ OLam $ \_X -> ORet _X
>         , {-CONST-} oTup $ \_A -> OLam $ \_X -> ORet _A
>         , {-SUM-} oTup $ \_E _D -> OLam $ \_X -> ORet $
>                     SIGMA (ENUMT _E) $ L $ "c" :. [.c. N $
>                        descOp :@ [_D -$ [NV c], _X -$ []]]
>         , {-PROD-} oTup $ \_D _D' -> OLam $ \_X -> ORet $
>                     TIMES (descOp @@ [_D, _X]) (descOp @@ [_D', _X])
>         , {-SIGMA-} oTup $ \_S _D -> OLam $ \_X -> ORet $
>                     SIGMA _S $ L $ "s" :. [.s. N $
>                       descOp :@ [_D -$ [NV s], _X -$ []]]
>         , {-PI-} oTup $ \_S _D -> OLam $ \_X -> ORet $
>                     PI _S $ L $ "s" :. [.s. N $
>                       descOp :@ [_D -$ [NV s], _X -$ []]]
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       dOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         Target SET

>   boxOp :: Op
>   boxOp = Op
>     { opName = "box"
>     , opArity = 4
>     , opTyTel = boxOpTy
>     , opRun = {-boxOpRun-} runOpTree $ oData
>         [ {-ID-} oTup $             oLams $ \ () _P x -> ORet (_P $$ A x)
>         , {-CONST-} oTup $ \ () ->  oLams $ \ () () () -> ORet UNIT
>         , {-SUM-} oTup $ \ () _D -> oLams $ \_X _P -> OPr $ oLams $ \c d ->
>              ORet $ boxOp @@ [_D $$ A c, _X, _P, d]
>         , {-PROD-} oTup $ \_D _D' -> oLams $ \_X _P -> OPr $ oLams $ \d d' ->
>              ORet $ TIMES (boxOp @@ [_D, _X, _P, d])
>                           (boxOp @@ [_D', _X, _P, d'])
>         , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _P -> OPr $ oLams $ \s d ->
>              ORet $ boxOp @@ [_D $$ A s, _X, _P, d]
>         , {-PI-} oTup $ \_S _D -> oLams $ \_X _P f ->
>              ORet $ PI _S $ L $ "s" :. [.s. N $
>                 boxOp :@ [_D -$ [NV s], _X -$ [] , _P -$ [] , f -$ [NV s]]]
>         ]
>     , opSimp = \_ _ -> empty
>     } where
>       boxOpTy =
>         "D" :<: desc :-: \dD ->
>         "X" :<: SET :-: \xX ->
>         "P" :<: ARR xX SET :-: \pP ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>         Target SET

>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBox"
>     , opArity = 5
>     , opTyTel = mapBoxOpTy
>     , opRun = {-mapBoxOpRun-} runOpTree $ oData
>       [ {-ID-} oTup $             oLams $ \ () () p x -> ORet (p $$ A x)
>       , {-CONST-} oTup $ \ () ->  oLams $ \ () () () () -> ORet VOID
>       , {-SUM-} oTup $ \ () _D -> oLams $ \_X _P p -> OPr $ oLams $ \c d ->
>            ORet $ mapBoxOp @@ [_D $$ A c, _X, _P, p, d]
>       , {-PROD-} oTup $ \_D _D' -> oLams $ \_X _P p -> OPr $ oLams $ \d d' ->
>            ORet $ PAIR (mapBoxOp @@ [_D, _X, _P, p, d])
>                        (mapBoxOp @@ [_D', _X, _P, p, d'])
>       , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _P p -> OPr $ oLams $ \s d ->
>            ORet $ mapBoxOp @@ [_D $$ A s, _X, _P, p, d]
>       , {-PI-} oTup $ \() _D -> oLams $ \_X _P p f ->
>            ORet $ L $ "s" :. [.s. N $
>              mapBoxOp :@ [_D -$ [NV s], _X -$ [] , _P -$ [] , p -$ [],
>                            f -$ [NV s]]]
>       ]
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy =  
>         "D" :<: desc :-: \ dD ->
>         "X" :<: SET :-: \ xX ->
>         "P" :<: ARR xX SET :-: \ pP ->
>         "p" :<: (pity $ "x" :<: xX :-: \ x -> Target $ pP $$ A x) :-: \ _ ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>          Target (boxOp @@ [dD,xX,pP,v])

>   mapOp = Op
>     { opName  = "map"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = {-mapOpRun-} runOpTree $ oData
>       [ {-ID-} oTup $ oLams $ \ () () f v -> ORet $ f $$ A v
>       , {-CONST-} oTup $ \ () -> oLams $ \ () () () a -> ORet a
>       , {-SUM-} oTup $ \ () _D -> oLams $ \_X _Y f -> OPr $ oLams $ \c d ->
>           ORet $ PAIR c (mapOp @@ [_D $$ A c, _X, _Y, f, d])
>       , {-PROD-} oTup $ \_D _D' -> oLams $ \_X _Y f -> OPr $ oLams $ \d d' ->
>           ORet $ PAIR (mapOp @@ [_D, _X, _Y, f, d])
>                       (mapOp @@ [_D', _X, _Y, f, d'])
>       , {-SIGMA-} oTup $ \ () _D -> oLams $ \_X _Y f -> OPr $ oLams $ \s d ->
>            ORet $ PAIR s (mapOp @@ [_D $$ A s, _X, _Y, f, d])
>       , {-PI-} oTup $ \() _D -> oLams $ \_X _Y f g ->
>            ORet $ L $ "s" :. [.s. N $
>              mapOp :@ [_D -$ [NV s], _X -$ [] , _Y -$ [] , f -$ [],
>                            g -$ [NV s]]]
>       ]
>     , opSimp  = mapOpSimp
>     } where
>         mapOpTy = 
>           "dD" :<: desc :-: \dD -> 
>           "xX" :<: SET :-: \xX ->
>           "yY" :<: SET :-: \yY ->
>           "f" :<: ARR xX yY :-: \f ->
>           "v" :<: (descOp @@ [dD, xX]) :-: \v -> 
>           Target (descOp @@ [dD, yY])
>         mapOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>         mapOpSimp [dD, xX, yY, f, N v] r
>           | equal (SET :>: (xX, yY)) r && 
>             equal (ARR xX yY :>: (f, identity)) r = pure v
>           where
>             identity = L $ "x" :. [.x. NV x]
>         mapOpSimp [dD, _, zZ, f, N (mOp :@ [_, xX, _, g, N v])] r
>           | mOp == mapOp = mapOpSimp args r <|> pure (mapOp :@ args)
>           where
>             comp f g = L $ "x" :. [.x. f -$ [g -$ [NV x]]]
>             args = [dD, xX, zZ, comp f g, N v]
>         mapOpSimp _ _ = empty

>   inductionOpMethodType = L $ "d" :. [.d.
>                      L $ "P" :. [._P. 
>                      PI (N $ descOp :@ [NV d, MU Nothing (NV d)])
>                         (L $ "x" :. [.x. 
>                          ARR (N $ boxOp :@ [NV d, MU Nothing (NV d), NV _P, NV x])
>                              (N (V _P :$ A (CON (NV x)))) ]) ] ]

>   inductionOpLabMethodType = L $ "l" :. [.l.
>                      L $ "d" :. [.d.
>                      L $ "P" :. [._P. 
>                      PI (N $ descOp :@ [NV d, MU (|(NV l)|) (NV d)])
>                         (L $ "x" :. [.x. 
>                          ARR (N $ boxOp :@ [NV d, MU (|(NV l)|) (NV d), NV _P, NV x])
>                              (N (V _P :$ A (CON (NV x)))) ]) ] ] ]


>   inductionOp :: Op
>   inductionOp = Op
>     { opName = "induction"
>     , opArity = 4
>     , opTyTel = inductionOpTy
>     , opRun = {-inductionOpRun-} runOpTree $
>         OLam $ \ _D -> OCon $ oLams $ \ v _P p -> ORet $
>           p $$ A v $$ A (mapBoxOp @@ [_D, MU Nothing _D, _P,
>             L $ "x" :. [.x. N $
>              inductionOp :@ [_D -$ [], NV x, _P -$ [], p -$ []]], v])
>     , opSimp = \_ _ -> empty
>     } where
>       inductionOpTy = 
>         "D" :<: desc :-: \dD ->
>         "v" :<: MU Nothing dD :-: \v ->
>         "P" :<: (ARR (MU Nothing dD) SET) :-: \pP ->
>         "p" :<: (inductionOpMethodType $$ A dD $$ A pP) :-: \p ->
>         Target (pP $$ A v)

>   branchesDOp = Op 
>     { opName   = "branchesD"
>     , opArity  = 1
>     , opTyTel  = bOpTy
>     , opRun    = runOpTree $
>         oData  [ oTup $ ORet UNIT
>                , oTup $ \ () _E -> ORet $
>                  TIMES desc
>                     (branchesDOp @@ [_E])
>                ]
>     , opSimp   = \_ _ -> empty
>     } where
>         bOpTy = "e" :<: enumU :-: \e ->
>                 Target SET



>   switchDOp = Op
>     { opName = "switchD"
>     , opArity = 3
>     , opTyTel = sOpTy
>     , opRun =  runOpTree $
>         OLam $ \_ -> OLam $ \bs ->
>         OCase (map (\x -> proj x bs) [0..])
>     , opSimp = \_ _ -> empty
>     } where
>         sOpTy = 
>           "e" :<: enumU :-: \e ->
>           "b" :<: (branchesDOp @@ [e]) :-: \b ->
>           "x" :<: ENUMT e :-: \x ->
>           Target desc
>         proj 0 bs = ORet (bs $$ Fst)
>         proj i bs = (proj (i - 1) (bs $$ Snd))



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


\subsection{Extending the Display Language}

> import -> KeywordConstructors where
>   KwMu :: Keyword

> import -> KeywordTable where
>   key KwMu        = "Mu"

> import -> DInTmParsersSpecial where
>   (AndSize, (|(DMU Nothing) (%keyword KwMu%) (sizedDInTm ArgSize)|)) :


> import -> MakeElabRules where

We elaborate list-like syntax for enumerations into the corresponding inductive
data. This cannot apply in general because it leads to infinite loops when
elaborating illegal values for some descriptions. Perhaps we should remove it
for enumerations as well.

>     makeElab' loc (MU l@(Just (NP r)) d :>: DVOID) | r == enumFakeREF = 
>         makeElab' loc (MU l d :>: DCON (DPAIR DZE DVOID))
>     makeElab' loc (MU l@(Just (NP r)) d :>: DPAIR s t) | r == enumFakeREF =
>         makeElab' loc (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))

More usefully, we elaborate a tag with a bunch of arguments by converting it
into the corresponding inductive data structure. This depends on the description
having a certain standard format, so it does not work in general.
\question{Can we make it more robust by looking at the description?}

>     makeElab' loc (MU l d :>: DTag s xs) =
>         makeElab' loc (MU l d :>: DCON (foldr DPAIR DVOID (DTAG s : xs)))


When elaborating |Mu| we can attach a label for display instead of the underlying
description. This is often useful when constructing user-visible data types. It
is not helpful when the description is a bound variable, however, so we check
for that case and do not label it.

>     makeElab' loc (SET :>: DMU Nothing d) = do
>         dt :=>: dv <- subElab loc (desc :>: d)
>         if shouldLabel dv
>             then do  (lt :=>: lv) <- eFaker 
>                      return $ MU (Just (N lt)) dt :=>: MU (Just lv) dv
>             else     return $ MU Nothing dt :=>: MU Nothing dv
>       where
>         shouldLabel :: VAL -> Bool
>         shouldLabel (NP (_ := DECL :<: _))  = False
>         shouldLabel _                       = True
 
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

The following cases turn vaguely list-like data into actual lists.
We don't want this in general, but it is useful in special cases (when the data
type is really supposed to be a list, as in |EnumD|).
\question{When else should we use this representation?}

>     distill _ (MU (Just (NP r)) _ :>: CON (PAIR ZE VOID)) | r == enumFakeREF =
>         return (DVOID :=>: CON (PAIR ZE VOID))

>     distill es (C ty@(Mu (Just (NP r) :?=: _)) :>:
>       C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID)))))
>       | r == enumFakeREF = do
>         Con (DPAIR _ (DPAIR s (DPAIR t _)) :=>: v) <- canTy  (distill es)
>                                                              (ty :>: c)
>         return ((DPAIR s t) :=>: CON v)


If we have a canonical value in |MU s|, where |s| starts with a finite sum,
then we can (probably) turn it into a tag applied to some arguments.

>     distill es (ty@(MU l s) :>: CON (PAIR t x)) | Just (e, f) <- sumlike s = do
>         m   :=>: tv  <- distill es (ENUMT e :>: t)
>         as  :=>: xv  <- distill es (descOp @@ [f tv, ty] :>: x)
>         case m of
>             DTAG s   -> return $ DTag s (unfold as)  :=>: CON (PAIR tv xv)
>             _        -> return $ DCON (DPAIR m as)   :=>: CON (PAIR tv xv)
>       where
>         unfold :: DInTmRN -> [DInTmRN]
>         unfold DU           = [] -- since DVOID gets turned into this first
>         unfold DVOID        = []
>         unfold (DPAIR s t)  = s : unfold t
>         unfold t            = [t]


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




> import -> DInTmConstructors where

> import -> DInTmPretty where

> import -> Pretty where

\subsection{Adding Primitive references in Cochon}

> import -> Primitives where
>   ("Desc", descREF) :
>   ("DescD", descDREF) :

\subsection{Bootstrapping}

> import -> RulesCode where
>   inDesc :: VAL
>   inDesc = SUMD constructors
>                (L $ "c" :. [.c. N $
>                    switchDOp :@ [ constructors , cases , NV c] ])
>       where constructors = (CONSE (TAG "idD")
>                            (CONSE (TAG "constD")
>                            (CONSE (TAG "sumD")
>                            (CONSE (TAG "prodD")
>                            (CONSE (TAG "sigmaD")
>                            (CONSE (TAG "piD")
>                             NILE))))))
>             cases = (PAIR (CONSTD UNIT) 
>                     (PAIR (SIGMAD SET (L $ K $ CONSTD UNIT))
>                     (PAIR (SIGMAD (enumU -$ []) (L $ "E" :. [._E.
>                                       (PRODD (PID (ENUMT (NV _E)) (LK IDD))
>                                              (CONSTD UNIT))]))
>                     (PAIR (PRODD IDD (PRODD IDD (CONSTD UNIT)))
>                     (PAIR (SIGMAD SET (L $ "S" :. [._S. 
>                                       (PRODD (PID (NV _S) (LK IDD)) 
>                                              (CONSTD UNIT))]))
>                     (PAIR (SIGMAD SET (L $ "S" :. [._S. 
>                                       (PRODD (PID (NV _S) (LK IDD)) 
>                                              (CONSTD UNIT))]))
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


The |sumlike| function determines whether a value representing a description
is a sum or a sigma from an enumerate. If so, it returns |Just| the enumeration
and a function from the enumeration to descriptions.
\question{Where should this live?}

>   sumlike :: VAL -> Maybe (VAL, VAL -> VAL)
>   sumlike (SUMD e b)            = Just (e, (b $$) . A)
>   sumlike (SIGMAD (ENUMT e) f)  = Just (e, (f $$) . A)
>   sumlike _                     = Nothing
