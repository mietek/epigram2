\section{Desc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Desc where

%endif

\question{Do the Formation/Introduction/\ldots names make sense?}
\question{How to handle the eliminators?}

Formation rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Desc-formation}
\UnaryInfC{|Set :>: Desc|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Desc :>: x|}
\RightLabel{Mu-formation}
\UnaryInfC{|Set :>: Mu x|}
\end{prooftree}

Introduction rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Desc-intro-1}
\UnaryInfC{|Desc :>: Done|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Set :>: A|}
\AxiomC{|X -> Desc :>: f|}
\RightLabel{Desc-intro-2}
\BinaryInfC{|Desc :>: Arg A f|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Set :>: H|}
\AxiomC{|Desc :>: x|}
\RightLabel{Desc-intro-3}
\BinaryInfC{|Desc :>: Ind H x|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|desc x (Mu x) :>: y|}
\RightLabel{Mu-intro}
\UnaryInfC{|Mu x :>: y|}
\end{prooftree}

Elimination rules:


\begin{prooftree}
\AxiomC{|Desc :>: x|}
\AxiomC{|Set :>: y|}
\RightLabel{desc-elim}
\BinaryInfC{|Set :>: desc(x,y)|}
\end{prooftree}

With the computational behavior:

< desc Done _ :-> Unit
< desc (Arg X f) Z :-> Sigma X (\a -> desc(f a, Z))
< desc (Ind H d) Z :-> Times (H -> Z) (desc(d,Z))

\begin{prooftree}
\AxiomC{|Desc :>: d|}
\AxiomC{|Set :>: D|}
\noLine
\BinaryInfC{|desc(d,D) :>: v|}
\AxiomC{|D -> Set :>: bp|}
\RightLabel{box-elim}
\BinaryInfC{|Set :>: box(d,D,bp,v)|}
\end{prooftree}

With the computation behavior:

< box Done _ _ _ :-> Unit
< box (Arg A f) d p v :-> box (f (fst v)) d p (snd v)
< box (Ind H x) d p v :-> Times ((y : H) -> p ((fst v) y)) 
<                               box(x,d,p,snd v)

\begin{prooftree}
\AxiomC{|Desc :>: d|}
\AxiomC{|Set :>: D|}
\AxiomC{|D -> Set :>: bp|}
\noLine
\TrinaryInfC{|(y : D) -> bp y :>: p|}
\AxiomC{|desc(d,D) :>: v|}
\RightLabel{mapbox-elim}
\BinaryInfC{|box(d,D,bp,v) :>: mapbox(d,D,bp,p,v)|}
\end{prooftree}

With the computational behavior:

< mapbox Done _ _ _ _ :-> Void
< mapbox (Arg A f) d bp p v :-> mapbox (f (fst v)) d bp p (snd v)
< mapbox (Ind H x) d bp p v :-> Pair (\y -> p ((fst v) y))
<                                    mapbox(x,d,bp,p,(snd v))

\begin{prooftree}
\AxiomC{|Desc :>: d|}
\AxiomC{|Mu d -> Set :>: bp|}
\AxiomC{|Mu d :>: v|}
\noLine
\TrinaryInfC{|(x : desc(d,Mu d)) -> box(d,Mu d, bp, x) -> bp (Con x) :>: p|}
\RightLabel{elim-elim}
\UnaryInfC{|p v (mapbox d (Mu d) bp (\x -> elim d bp p x) v|}
\end{prooftree}

With the computational behavior:

< elim d bp p (Con v) :-> p v (mapbox(d, Mu d, bp, (\x -> elim d bp p x), v))

Equality rules:

< eqGreen(Desc, Done, Desc, Done) :-> Trivial
< eqGreen(Desc, Arg x1 y1, Desc, Arg x2 y2) :-> 
<     And (eqGreen(Set, x1, Set, x2))
<         (eqGreen(x1 -> Desc, y1, x1 -> Desc, y2))
< eqGreen(Desc, Ind x1 y1, Desc, Ind x2 y2) :->
<     And (eqGreen(Set, x1, Set, x2))
<         (eqGreen(Desc, y1, Desc, y2))
< eqGreen(Mu d1, x1, Mu d2, x2) :->
<     eqGreen(descOp @@ [d1, Mu d1], Out x1,
<             descOp @@ [d2, Mu d2], Out x2) 


> import -> CanConstructors where
>   Mu     :: Labelled Id t -> Can t

> import -> TraverseCan where
>   traverse f (Mu l) = (|Mu (traverse f l)|)

> import -> HalfZipCan where
>   halfZip (Mu t0) (Mu t1) = (| Mu (halfZip t0 t1) |)

> import -> BootstrapDesc where
>   inDesc :: VAL
>   inDesc = ARG (ENUMT constructors) $
>                eval (L $ "" :. [.x. 
>                 N $ switchDOp :@ [constructors, cases, NV x]]) B0
>       where constructors = (CONSE (TAG "done")
>                             (CONSE (TAG "arg")
>                              (CONSE (TAG "ind")
>                               (CONSE (TAG "ind1")
>                                NILE))))
>             cases = PAIR DONE 
>                     (PAIR (ARG SET (L $ "" :. [.s. IND (NV s) DONE]))
>                      (PAIR (ARG SET (L $ "" :. [.h. IND1 DONE]))
>                       (PAIR (IND1 DONE)
>                        VOID)))
>   descFakeREF :: REF
>   descFakeREF = [("Primitive", 0), ("Desc", 0)] := (FAKE :<: SET)
>   desc :: VAL
>   desc = MU (Just (N (P descFakeREF))) inDesc
>
>   descREF :: REF
>   descREF = [("Primitive", 0), ("Desc", 0)] := (DEFN desc :<: SET)

> import -> Primitives where
>   ("Desc", descREF) :

> import -> CanPats where
>   pattern MU l x  = C (Mu (l :?=: Id x))
>   pattern DONE = CON (PAIR ZE VOID)
>   pattern ARG s d = CON (PAIR (SU ZE) (PAIR s (PAIR d VOID)))
>   pattern IND h d = CON (PAIR (SU (SU ZE)) (PAIR h (PAIR d VOID)))
>   pattern IND1 d = CON (PAIR (SU (SU (SU ZE))) (PAIR d VOID))

> import -> DisplayCanPats where
>   pattern DMU l x  = DC (Mu (l :?=: Id x))
>   pattern DDONE = DCON (DPAIR DZE DVOID)
>   pattern DARG s d = DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR d DVOID)))
>   pattern DIND h d = DCON (DPAIR (DSU (DSU DZE)) (DPAIR h (DPAIR d DVOID)))
>   pattern DIND1 d = DCON (DPAIR (DSU (DSU (DSU DZE))) (DPAIR d DVOID))

> import -> SugarTactics where
>   muTac t = can $ Mu (Nothing :?=: Id t)
>   descTac = done (desc :<: SET)
>   doneTac =  conTac (pairTac zeTac voidTac)
>   argTac x y = conTac (pairTac (suTac zeTac) (pairTac x (pairTac y voidTac)))
>   indTac x y = conTac (pairTac (suTac (suTac zeTac)) (pairTac x (pairTac y voidTac)))
>   ind1Tac x = conTac (pairTac (suTac (suTac (suTac zeTac))) (pairTac x voidTac))

> import -> CanPretty where
>   pretty (Mu (Just l   :?=: _))     = pretty l
>   pretty (Mu (Nothing  :?=: Id t))  = wrapDoc
>       (kword KwMu <+> pretty t ArgSize)
>       ArgSize

> import -> CanTyRules where
>   canTy chev (Set :>: Mu (ml :?=: Id x))     = do
>     mlv <- traverse (chev . (SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (desc :>: x)
>     return $ Mu (mlv :?=: Id xxv)
>   canTy chev (t@(Mu (_ :?=: Id x)) :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [x, C t] :>: y)
>     return $ Con yyv

> import -> ElimTyRules where
>   elimTy chev (_ :<: t@(Mu (_ :?=: Id d))) Out = return (Out, descOp @@ [d , C t])


> import -> Operators where
>   descOp :
>   boxOp :
>   mapBoxOp :
>   elimOp :
>   switchDOp :
>   mapOp :

> import -> OpCompile where
>   ("elimOp", [d,v,bp,p]) -> App (Var "__elim") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   ("SwitchD", [e,b,x]) -> App (Var "__switch") [x, b]
>   ("map", [d,a,b,f,x]) -> App (Var "__map") [d, f, x]

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "descOp"
>     , opArity = 2
>     , opTyTel = dOpTy
>     , opRun = dOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       dOpTy =
>         "x" :<: desc :-: \x ->
>         "y" :<: SET :-: \y ->
>         Ret SET
>       dOpRun :: [VAL] -> Either NEU VAL
>       dOpRun [DONE,y]    = Right UNIT
>       dOpRun [ARG x y,z] = Right $
>         eval [.x.y.z. 
>              SIGMA (NV x) . L $ "" :. [.a.
>              (N (descOp :@ [y $# [a],NV z]))
>              ]] $ B0 :< x :< y :< z
>       dOpRun [IND x y,z] = Right (TIMES (ARR x z) (descOp @@ [y,z]))
>       dOpRun [IND1 x,z] = Right (TIMES z (descOp @@ [x,z]))
>       dOpRun [N x,_]     = Left x


>   boxOp :: Op
>   boxOp = Op
>     { opName = "boxOp"
>     , opArity = 4
>     , opTyTel = boxOpTy
>     , opRun = boxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       boxOpTy =
>         "w" :<: desc :-: \w ->
>         "x" :<: SET :-: \x ->
>         "y" :<: ARR x SET :-: \y ->
>         "z" :<: (descOp @@ [w,x]) :-: \z ->
>         Ret SET
>       boxOpRun :: [VAL] -> Either NEU VAL
>       boxOpRun [DONE   ,d,p,v] = Right UNIT
>       boxOpRun [ARG a f,d,p,v] = Right $ opRunArgTerm
>                                          $$ A a $$ A f $$ A d $$ A p $$ A v
>       boxOpRun [IND h x,d,p,v] = Right $ opRunIndTerm
>                                          $$ A h $$ A x $$ A d $$ A p $$ A v
>       boxOpRun [IND1 x,d,p,v] = Right $ opRunInd1Term
>                                         $$ A x $$ A d $$ A p $$ A v
>       boxOpRun [N x    ,_,_,_] = Left x
>       opRunArgTerm = trustMe (opRunArgType :>: opRunArgTac) 
>       opRunIndTerm = trustMe (opRunIndType :>: opRunIndTac)
>       opRunInd1Term = trustMe (opRunInd1Type :>: opRunInd1Tac)
>
>       opRunTypeTac arg = piTac setTac
>                                (\y ->
>                                 piTac (arrTac (use y done)
>                                               setTac)
>                                       (\z -> 
>                                        arrTac (useOp descOp [ arg
>                                                             , use y done ] done)
>                                               setTac))
>       opRunArgType = trustMe (SET :>: opRunArgTypeTac)
>       opRunArgTypeTac = piTac setTac
>                               (\x ->
>                                piTac (arrTac (use x done)
>                                              descTac) 
>                                      (\f ->
>                                       opRunTypeTac (argTac (use x done)
>                                                            (use f done))))
>       opRunArgTac = lambda $ \a ->
>                     lambda $ \f ->
>                     lambda $ \d ->
>                     lambda $ \p ->
>                     lambda $ \v -> 
>                     useOp boxOp [ f @@@ [use v . apply Fst $ done]
>                                 , use d done 
>                                 , use p done
>                                 , use v . apply Snd $ done ] done
>
>       opRunIndType = trustMe (SET :>: opRunIndTypeTac) 
>       opRunIndTypeTac = piTac setTac
>                               (\h ->
>                                piTac descTac
>                                      (\x ->
>                                       opRunTypeTac (indTac (use h done)
>                                                            (use x done))))
>       opRunIndTac = lambda $ \h ->
>                     lambda $ \x ->
>                     lambda $ \d ->
>                     lambda $ \p ->
>                     lambda $ \v ->
>                     timesTac (piTac (use h done)
>                                     (\y -> 
>                                      p @@@ [use v . apply Fst . 
>                                                     apply (A $ use y done) $ done]))
>                              (useOp boxOp [ use x done
>                                           , use d done
>                                           , use p done
>                                           , use v . apply Snd $ done ] done)
>       opRunInd1Type = trustMe (SET :>: opRunInd1TypeTac) 
>       opRunInd1TypeTac = piTac descTac
>                                (\x ->
>                                 opRunTypeTac (ind1Tac (use x done)))
>       opRunInd1Tac = lambda $ \x ->
>                      lambda $ \d ->
>                      lambda $ \p ->
>                      lambda $ \v ->
>                      timesTac (p @@@ [use v . apply Fst $ done])
>                               (useOp boxOp [ use x done
>                                            , use d done
>                                            , use p done
>                                            , use v . apply Snd $ done ] done)


>   mapBoxOp :: Op
>   mapBoxOp = Op
>     { opName = "mapBoxOp"
>     , opArity = 5
>     , opTyTel = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy =  
>         "D" :<: desc :-: \ dD ->
>         "X" :<: SET :-: \ xX ->
>         "P" :<: ARR xX SET :-: \ pP ->
>         "p" :<: (pity $ "x" :<: xX :-: \ x -> Ret $ pP $$ A x) :-: \ _ ->
>         "v" :<: (descOp @@ [dD,xX]) :-: \v ->
>          Ret (boxOp @@ [dD,xX,pP,v])
>       mapBoxOpRun :: [VAL] -> Either NEU VAL
>       mapBoxOpRun [DONE,d,bp,p,v] = Right VOID
>       mapBoxOpRun [ARG a f,d,bp,p,v] = Right $ mapBoxArgTerm
>                                                $$ A a $$ A f $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [IND h x,d,bp,p,v] = Right $ mapBoxIndTerm 
>                                                $$ A h $$ A x $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [IND1 x,d,bp,p,v] = Right $ mapBoxInd1Term
>                                                 $$ A x $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [N x    ,_, _,_,_] = Left x
>       mapBoxArgTerm = trustMe (mapBoxArgType :>: mapBoxArgTac) 
>       mapBoxIndTerm = trustMe (mapBoxIndType :>: mapBoxIndTac)
>       mapBoxInd1Term = trustMe (mapBoxInd1Type :>: mapBoxInd1Tac) 
>
>       mapBoxTypeTac arg = piTac setTac
>                                 (\d ->
>                                  piTac (arrTac (use d done)
>                                                setTac)
>                                        (\bp ->
>                                         arrTac (piTac (use d done)
>                                                       (\y ->
>                                                        bp @@@ [use y done]))
>                                                (piTac (useOp descOp [ arg
>                                                                     , use d done ] done)
>                                                       (\v ->
>                                                        useOp boxOp [ arg
>                                                                    , use d done
>                                                                    , use bp done
>                                                                    , use v done] done))))
>       mapBoxIndType = trustMe (SET :>: mapBoxIndTypeTac)
>       mapBoxIndTypeTac = piTac setTac
>                                (\h ->
>                                 piTac descTac
>                                       (\x ->
>                                        mapBoxTypeTac (indTac (use h done)
>                                                              (use x done))))
>       mapBoxIndTac = lambda $ \h ->
>                      lambda $ \x ->
>                      lambda $ \d ->
>                      lambda $ \bp ->
>                      lambda $ \p ->
>                      lambda $ \v ->
>                      pairTac (lambda $ \y ->
>                               p @@@ [use v .
>                                      apply Fst .
>                                      apply (A (use y done)) 
>                                      $ done])
>                               (useOp mapBoxOp [ use x done
>                                               , use d done
>                                               , use bp done
>                                               , use p done
>                                               , use v . apply Snd $ done ] done)
>       mapBoxInd1Type = trustMe (SET :>: mapBoxInd1TypeTac)
>       mapBoxInd1TypeTac = piTac descTac
>                                 (\x ->
>                                  mapBoxTypeTac (ind1Tac (use x done)))
>       mapBoxInd1Tac = lambda $ \x ->
>                       lambda $ \d ->
>                       lambda $ \bp ->
>                       lambda $ \p ->
>                       lambda $ \v ->
>                       pairTac (p @@@ [use v .
>                                       apply Fst 
>                                       $ done])
>                               (useOp mapBoxOp [ use x done
>                                               , use d done
>                                               , use bp done
>                                               , use p done
>                                               , use v . apply Snd $ done ] done)
>       mapBoxArgType = trustMe (SET :>: mapBoxArgTypeTac)
>       mapBoxArgTypeTac = piTac setTac
>                                (\a -> 
>                                 piTac (arrTac (use a done)
>                                               descTac)
>                                       (\f -> 
>                                        mapBoxTypeTac (argTac (use a done)
>                                                              (use f done))))
>       mapBoxArgTac = lambda $ \a ->
>                      lambda $ \f ->
>                      lambda $ \d ->
>                      lambda $ \bp ->
>                      lambda $ \p ->
>                      lambda $ \v ->
>                      useOp mapBoxOp [ f @@@ [ use v . apply Fst $ done ]
>                                     , use d done
>                                     , use bp done
>                                     , use p done
>                                     , use v . apply Snd $ done ] done


>   elimOpMethodTypeType = trustMe . (SET :>:) $
>     piTac descTac $ \d -> arrTac (arrTac (muTac (var d)) setTac) setTac
>   elimOpMethodType = trustMe . (elimOpMethodTypeType :>:) $
>     lambda $ \d -> lambda $ \pP ->
>     piTac (useOp descOp [ var d, muTac (var d) ] done) $ \x ->
>     arrTac (useOp boxOp [ var d, muTac (var d), var pP, var x ] done) $
>     pP @@@ [conTac (var x)]

>   elimOpLabMethodTypeType = trustMe . (SET :>:) $
>     arrTac setTac $ piTac descTac $ \d -> arrTac (arrTac (muTac (var d)) setTac) setTac
>   elimOpLabMethodType = trustMe . (elimOpLabMethodTypeType :>:) $
>     lambda $ \l -> lambda $ \d -> lambda $ \pP ->
>     piTac (useOp descOp [var d, can $ Mu (Just (var l) :?=: Id (var d))] done) $ \x ->
>     arrTac (useOp boxOp [var d, can $ Mu (Just (var l) :?=: Id (var d)), var pP, var x ] done) $
>     pP @@@ [conTac (var x)]

>   elimOp :: Op
>   elimOp = Op
>     { opName = "elimOp"
>     , opArity = 4
>     , opTyTel = elimOpTy
>     , opRun = elimOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimOpTy = 
>         "d" :<: desc :-: \d ->
>         "v" :<: MU Nothing d :-: \v ->
>         "P" :<: (ARR (MU Nothing d) SET) :-: \bp ->
>         "p" :<: (elimOpMethodType $$ A d $$ A bp) :-: \p ->
>         Ret (bp $$ A v)
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [d,CON v,bp,p] = Right $ elimOpTerm
>                                              $$ A d $$ A bp $$ A p $$ A v
>       elimOpRun [_,N x, _,_] = Left x
>
>       elimOpTerm = trustMe (elimOpType :>: elimOpTac) 
>       elimOpType = trustMe (SET :>: elimOpTypeTac)
>       elimOpTypeTac = piTac descTac $ \d ->
>                       piTac (arrTac (muTac (var d)) setTac) $ \bp ->
>                       arrTac (chk (return (elimOpMethodType :<: elimOpMethodTypeType)
>                                    `useTac` A (var d) `useTac` A (var bp))) $
>                       piTac (useOp descOp [var d, muTac (var d) ] done) $ \v ->
>                       bp @@@ [conTac $ var v]
>
>       elimOpTac = lambda $ \d ->  -- (d : Desc)
>                   lambda $ \bp -> -- (bp : Mu d -> Set)
>                   lambda $ \p ->  -- (x : descOp d (Mu d)) -> (boxOp d (Mu d) bp x) -> bp (Con x)
>                   lambda $ \v ->  -- (v : descOp d (Mu d))
>                   p @@@ [ use v done
>                         , useOp mapBoxOp [ use d done
>                                          , muTac (use d done)
>                                          , use bp done
>                                          , lambda $ \x ->
>                                            useOp elimOp [ use d done
>                                                         , use x done 
>                                                         , use bp done
>                                                         , use p done ] done 
>                                          , use v done ] done ]

>   switchDOp = Op
>     { opName = "SwitchD"
>     , opArity = 3
>     , opTyTel = sOpTy
>     , opRun = sOpRun
>     , opSimp = \_ _ -> empty
>     } where
>         sOpTy = 
>           "e" :<: enumU :-: \e ->
>           "b" :<: (branchesOp @@ [e , L (K desc) ]) :-: \b ->
>           "x" :<: ENUMT e :-: \x ->
>           Ret desc
>         sOpRun :: [VAL] -> Either NEU VAL
>         sOpRun [CONSE t e' , ps , ZE] = Right $ ps $$ Fst
>         sOpRun [CONSE t e' , ps , SU n] = Right $
>           switchDOp @@ [ e' 
>                        , ps $$ Snd
>                        , n ]
>         sOpRun [_ , _ , N n] = Left n
>         sOpRun vs = error ("Desc.SwitchD.sOpRun: couldn't handle " ++ show vs)

>   mapOp = Op
>     { opName  = "map"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = mapOpRun
>     , opSimp  = mapOpSimp
>     } where
>         mapOpTy = 
>           "d" :<: desc :-: \d -> 
>           "a" :<: SET :-: \a ->
>           "b" :<: SET :-: \b ->
>           "f" :<: ARR a b :-: \f ->
>           "x" :<: (descOp @@ [d, a]) :-: \x -> 
>           Ret (descOp @@ [d, b])
>
>         mapOpRun :: [VAL] -> Either NEU VAL
>         mapOpRun [DONE,    a, b, f, x] = Right VOID
>         mapOpRun [ARG s d, a, b, f, x] = Right $
>           eval [.s.d.a.b.f.x.
>                 PAIR (N (V x :$ Fst))
>                      (N $ mapOp :@ [ N $ V d :$ A (N $ V x :$ Fst)
>                                    , NV a, NV b, NV f, N (V x :$ Snd)
>                                    ])
>           ] $ B0 :< s :< d :< a :< b :< f :< x
>         mapOpRun [IND h d, a, b, f, x] = Right $
>           eval [._H.d.a.b.f.x.
>                 PAIR (L $ "h" :. [.h. N $ V f :$ A (N $ V x :$ Fst :$ A (NV h))])
>                      (N $ mapOp :@ [ NV d, NV a, NV b, NV f
>                                    , N (V x :$ Snd) ])
>           ] $ B0 :< h :< d :< a :< b :< f :< x
>         mapOpRun [IND1 d,  a, b, f, x] = Right $
>           eval [.d.a.b.f.x.
>                 PAIR (N $ V f :$ A (N $ V x :$ Fst))
>                      (N $ mapOp :@ [ NV d, NV a, NV b, NV f
>                                    , N (V x :$ Snd) ])
>           ] $ B0 :< d :< a :< b :< f :< x
>         mapOpRun [N d,     a, b, f, x] = Left d
>
>         mapOpSimp :: Alternative m => [VAL] -> Root -> m NEU
>         mapOpSimp [d, a, b, f, N x] r
>           | equal (ARR a b :>: (f, identity)) r = pure x
>           where
>             identity = eval (L ("x" :. [.x. NV x])) B0
>         mapOpSimp [d, _, c, f, N (mOp :@ [_, a, _, g, N x])] r
>           | mOp == mapOp = mapOpSimp args r <|> pure (mapOp :@ args)
>           where
>             comp f g = eval
>               [.f.g.
>                L ("x" :. [.x. N (V f :$ A (N $ V g :$ A (NV x)))])
>               ] $ B0 :< f :< g
>             args = [d, a, c, comp f g, N x]
>         mapOpSimp _ _ = empty



As some useful syntactic sugar, we let inductive types elaborate
lists (so |[]| becomes |@[0]| and |[s , t]| becomes |@ [1 s t]|).

> import -> ElaborateRules where
>     elaborate b (MU l d :>: DVOID) =
>         elaborate b (MU l d :>: DCON (DPAIR DZE DVOID))
>     elaborate b (MU l d :>: DPAIR s t) =
>         elaborate b (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))

To avoid an infinite loop when distilling, we have to be a little cleverer
and call canTy directly rather than letting distill do it for us.

> import -> DistillRules where
>     distill _ (MU _ _ :>: CON (PAIR ZE VOID)) =
>         return (DVOID :=>: CON (PAIR ZE VOID))
>     distill es (C ty@(Mu _) :>: C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID))))) = do
>         Con (DPAIR _ (DPAIR s (DPAIR t DVOID)) :=>: v) <- canTy (distill es) (ty :>: c)
>         return (DPAIR s t :=>: CON v)
>         