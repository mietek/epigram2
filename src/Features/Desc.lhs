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
>   pattern MU l x      = C (Mu (l :?=: Id x))
>   pattern IDD         = CON (PAIR  ZE                      
>                                    VOID)
>   pattern CONSTD x    = CON (PAIR  (SU ZE)                 
>                                    (PAIR x VOID))
>   pattern PRODD d d'  = CON (PAIR  (SU (SU ZE))            
>                                    (PAIR d d'))
>   pattern SIGMAD s t  = CON (PAIR  (SU (SU (SU ZE)))
>                                    (PAIR s t))
>   pattern PID s t     = CON (PAIR  (SU (SU (SU (SU ZE))))
>                                    (PAIR s t))

> import -> CanDisplayPats where
>   pattern DMU l x      = DC (Mu (l :?=: Id x))
>   pattern DIDD         = DCON (DPAIR  DZE 
>                                       DVOID)
>   pattern DCONSTD x    = DCON (DPAIR  (DSU DZE)
>                                       (DPAIR x DVOID))
>   pattern DPRODD d d'  = DCON (DPAIR  (DSU (DSU DZE))
>                                       (DPAIR d d'))
>   pattern DSIGMAD s t  = DCON (DPAIR  (DSU (DSU (DSU DZE)))
>                                       (DPAIR s t))
>   pattern DPID s t     = DCON (DPAIR  (DSU (DSU (DSU (DSU DZE))))
>                                       (DPAIR s t))

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
>   inductionOp :
>   switchDOp :

> import -> OpCompile where
>   ("induction", [d,v,bp,p]) -> App (Var "__induction") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   ("switchD", [e,b,x]) -> App (Var "__switch") [x, b]

> import -> OpCode where
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
>       dOpRun [IDD,           _X]  = Right _X
>       dOpRun [CONSTD _Z ,    _X]  = Right _Z
>       dOpRun [PRODD _D _D',  _X]  = Right $ TIMES  (descOp @@ [ _D , _X ])
>                                                    (descOp @@ [ _D', _X ])
>       dOpRun [SIGMAD _S _T,  _X]  = Right $ SIGMA  _S . 
>                                                    L $ HF "s" $ \s ->
>                                                    descOp @@ [ _T $$ A s, _X ]
>       dOpRun [PID _S _T,     _X]  = Right $ PI  _S . 
>                                                 L $ HF "s" $ \s ->
>                                                 descOp @@ [ _T $$ A s, _X ]
>       dOpRun [N _D,          _]   = Left _D

%if False

>       dOpRun vs = error ("Desc.descOp.dOpRun: couldn't handle " ++ show vs)

%endif

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
>       boxOpRun [IDD ,          _X, _P, x ]  = 
>           Right $ _P $$ A x
>       boxOpRun [CONSTD _Z ,    _X, _P, x]   = 
>           Right $ _Z
>       boxOpRun [PRODD _D _D',  _X, _P, dd'] = 
>           let d  = dd' $$ Fst
>               d' = dd' $$ Snd 
>           in Right $ TIMES  (boxOp @@ [_D, _X, _P, d])
>                             (boxOp @@ [_D', _X, _P, d'])
>       boxOpRun [SIGMAD _S _T,  _X, _P, ab]  = 
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in Right $ boxOp @@ [_T $$ A a, _X, _P, b]
>       boxOpRun [PID _S _T,     _X, _P, f]  =
>           Right $ PI  _S . 
>                       L $ HF "s" $ \s -> 
>                       boxOp @@ [_T $$ A s, _X, _P, f $$ A s]
>       boxOpRun [N x,           _,_,_] = 
>           Left x

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
>       mapBoxOpRun [IDD,            _X, _P, _R, v]   = 
>           Right $ _R $$ A v
>       mapBoxOpRun [CONSTD _Z,      _X, _P, _R, z]   = 
>           Right z
>       mapBoxOpRun [PRODD _D _D',   _X, _P, _R, dd'] = 
>           let d  = dd' $$ Fst
>               d' = dd' $$ Snd 
>           in Right $ PAIR  (mapBoxOp @@ [_D,  _X, _P, _R, d])
>                            (mapBoxOp @@ [_D', _X, _P, _R, d'])
>       mapBoxOpRun [SIGMAD _S _T,   _X, _P, _R, ab]  =
>           let a = ab $$ Fst
>               b = ab $$ Snd
>           in Right $ mapBoxOp @@ [_T $$ A a, _X, _P, _R, b]
>       mapBoxOpRun [PID _S _T,      _X, _P, _R, f]   =
>           Right $ L . HF "s" $ \s ->
>                   mapBoxOp @@ [_T $$ A s, _X, _P, _R, f $$ A s]
>       mapBoxOpRun [N x,            _, _,_,_]        = 
>           Left x


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
>         mapOpRun [IDD, _X, _Y, sig, x] = Right $ sig $$ A x
>         mapOpRun [CONSTD _Z, _X, _Y, sig, z] = Right z
>         mapOpRun [PRODD _D _D', _X, _Y, sig, dd'] = 
>             let d  = dd' $$ Fst
>                 d' = dd' $$ Snd 
>             in 
>               Right $ PAIR  (mapOp @@ [_D,  _X, _Y, sig, d])
>                             (mapOp @@ [_D', _X, _Y, sig, d'])
>         mapOpRun [SIGMAD _S _T, _X, _Y, sig, ab] = 
>             let a = ab $$ Fst
>                 b = ab $$ Snd
>             in
>               Right $ PAIR a (mapOp @@ [_T $$ A a, _X, _Y, sig, b])
>         mapOpRun [PID _S _T, _X, _Y, sig, f] =
>             Right $  L . HF "s" $ \s ->
>                      mapOp @@ [_T $$ A s, _X, _Y, sig, f $$ A s]
>         mapOpRun [N d,     a, b, f, x] = Left d


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
>         sOpRun [CONSE t e', ps, ZE]   = Right $ 
>             ps $$ Fst
>         sOpRun [CONSE t e', ps, SU n] = Right $
>             switchDOp @@ [ e' , ps $$ Snd , n ]
>         sOpRun [_, _, N n] = Left n

%if False

>         sOpRun vs = error ("Desc.SwitchD.sOpRun: couldn't handle " ++ show vs)

%endif

\subsection{Plugging Axioms in}

> import -> Axioms where

> import -> AxCode where

> import -> MakeElabRules where
>     makeElab' loc (MU l d :>: DVOID) =
>         makeElab' loc (MU l d :>: DCON (DPAIR DZE DVOID))
>     makeElab' loc (MU l d :>: DPAIR s t) =
>         makeElab' loc (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))
>     makeElab' loc (SET :>: DMU Nothing d) = do
>         lt :=>: lv <- EFake True Bale
>         dt :=>: dv <- subElab loc (desc :>: d)
>         return $ MU (Just (N lt)) dt :=>: MU (Just lv) dv

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
>         makeElab' loc (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s t)))
>     makeElab' loc (SET :>: DMU Nothing d) = do
>         lt :=>: lv <- EFake True Bale
>         dt :=>: dv <- subElab loc (desc :>: d)
>         return $ MU (Just (N lt)) dt :=>: MU (Just lv) dv
 
> import -> DistillRules where
>     distill _ (MU _ _ :>: CON (PAIR ZE VOID)) =
>         return (DVOID :=>: CON (PAIR ZE VOID))
>     distill es (C ty@(Mu _) :>: C c@(Con (PAIR (SU ZE) (PAIR _ _)))) = do
>         Con (DPAIR _ (DPAIR s t) :=>: v) <- canTy (distill es) (ty :>: c)
>         return (DPAIR s t :=>: CON v)

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
>                             (CONSE (TAG "constD")
>                              (CONSE (TAG "prodD")
>                               (CONSE (TAG "sigmaD")
>                                (CONSE (TAG "piD")
>                                 NILE)))))
>             cases = PAIR (CONSTD UNIT) 
>                     (PAIR (SIGMAD SET (L $ K $ CONSTD UNIT))
>                      (PAIR (PRODD IDD IDD)
>                       (PAIR (SIGMAD SET (L $ HF "S" $ \_S -> 
>                                          PID _S (L $ K IDD)))
>                        (PAIR (SIGMAD SET (L $ HF "S" $ \_S -> 
>                                          PID _S (L $ K IDD)))
>                         VOID))))
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
 