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
>   Mu     :: t -> Can t

> import -> TraverseCan where
>   traverse f (Mu x)     = (|Mu (f x)|)

> import -> HalfZipCan where
>   halfZip (Mu t0) (Mu t1) = Just (Mu (t0,t1))

> import -> CanPats where
>   pattern MU x     = C (Mu x)
>   pattern DONE = CON (PAIR ZE VOID)
>   pattern ARG s d = CON (PAIR (SU ZE) (PAIR s (PAIR d VOID)))
>   pattern IND h d = CON (PAIR (SU (SU ZE)) (PAIR h (PAIR d VOID)))
>   pattern IND1 d = CON (PAIR (SU (SU (SU ZE))) (PAIR d VOID))


> import -> SugarTactics where
>   muTac t = can $ Mu t
>   descTac = done (desc :<: SET)
>   doneTac =  conTac (pairTac zeTac voidTac)
>   argTac x y = conTac (pairTac (suTac zeTac) (pairTac x (pairTac y voidTac)))
>   indTac x y = conTac (pairTac (suTac (suTac zeTac)) (pairTac x (pairTac y voidTac)))
>   ind1Tac x = conTac (pairTac (suTac (suTac (suTac zeTac))) (pairTac x voidTac))

> import -> CanPretty where
>   prettyCan (Mu t) = parens (text "Mu" <+> pretty t)

> import -> CanTyRules where
>   canTy chev (Set :>: Mu x)     = do
>     xxv@(x :=>: xv) <- chev (desc :>: x)
>     return $ Mu xxv
>   canTy chev (Mu x :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [x, MU x] :>: y)
>     return $ Con yyv

> import -> ElimTyRules where
>   elimTy chev (_ :<: Mu d) Out = return (Out, descOp @@ [d , MU d])


> import -> Operators where
>   descOp :
>   boxOp :
>   mapBoxOp :
>   elimOp :
>   switchDOp :

> import -> OpCompile where
>   ("elimOp", [d,v,bp,p]) -> App (Var "__elim") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   ("SwitchD", [e,b,x]) -> App (Var "__switch") [x, b]

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "descOp"
>     , opArity = 2
>     , opTy = dOpTy
>     , opRun = dOpRun
>     } where
>       dOpTy chev [x,y] = do
>                  (x :=>: xv) <- chev (desc :>: x)
>                  (y :=>: yv) <- chev (SET :>: y)
>                  return $ ([ x :=>: xv
>                            , y :=>: yv ]
>                           , SET)
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
>     , opTy = boxOpTy
>     , opRun = boxOpRun
>     } where
>       boxOpTy chev [w,x,y,z] = do
>         (w :=>: wv) <- chev (desc :>: w)
>         (x :=>: xv) <- chev (SET :>: x)
>         (y :=>: yv) <- chev (ARR xv SET :>: y)
>         (z :=>: zv) <- chev (descOp @@ [wv,xv] :>: z)
>         return ([ w :=>: wv
>                 , x :=>: xv
>                 , y :=>: yv
>                 , z :=>: zv ]
>                , SET)
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
>     , opTy = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     } where
>       mapBoxOpTy chev [x,d,bp,p,v] = do 
>           (x :=>: xv) <- chev (desc :>: x)
>           (d :=>: dv) <- chev (SET :>: d)
>           (bp :=>: bpv) <- chev (ARR dv SET :>: bp)
>           (p :=>: pv) <- chev (PI dv (eval [.bpv. L $ "" :. 
>                                                 [.y. N (V bpv :$ A (NV y))]
>                                               ] $ B0 :< bpv)
>                                 :>: p)
>           (v :=>: vv) <- chev (descOp @@ [xv,dv] :>: v)
>           return ([ x :=>: xv
>                   , d :=>: dv
>                   , bp :=>: bpv
>                   , p :=>: pv
>                   , v :=>: vv ]
>                  , boxOp @@ [xv,dv,bpv,vv])
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

 
>   elimOp :: Op
>   elimOp = Op
>     { opName = "elimOp"
>     , opArity = 4
>     , opTy = elimOpTy
>     , opRun = elimOpRun
>     } where
>       elimOpTy chev [d,v,bp,p] = do
>         (d :=>: dv) <- chev (desc :>: d)
>         (v :=>: vv) <- chev (MU dv :>: v)
>         (bp :=>: bpv) <- chev (ARR (MU dv) SET :>: bp)
>         (p :=>: pv) <- chev (PI (descOp @@ [dv,MU dv]) 
>                     (eval [.d.bp.v. L $ "" :. [.x. 
>                         ARR (N (boxOp :@ [NV d,MU (NV d),NV bp,NV x]))
>                             (N (V bp :$ A (CON (NV x))))]
>                         ] $ B0 :< dv :< bpv :< vv) :>: p)
>         return ([ d :=>: dv
>                 , v :=>: vv 
>                 , bp :=>: bpv
>                 , p :=>: pv ]
>                 , bpv $$ A vv)
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [d,CON v,bp,p] = Right $ elimOpTerm
>                                          $$ A d $$ A bp $$ A p $$ A v
>       elimOpRun [_,N x, _,_] = Left x
>
>       elimOpTerm = trustMe (elimOpType :>: elimOpTac) 
>       elimOpType = trustMe (SET :>: elimOpTypeTac)
>       elimOpTypeTac = piTac descTac
>                             (\d ->
>                              piTac (arrTac (muTac (use d done))
>                                            setTac)
>                                    (\bp ->
>                                     arrTac (piTac (useOp descOp [ use d done
>                                                                 , muTac (use d done) ] done)
>                                                   (\x ->
>                                                    arrTac (useOp boxOp [ use d done
>                                                                        , muTac (use d done)
>                                                                        , use bp done
>                                                                        , use x done ] done)
>                                                           (bp @@@ [conTac (use x done)])))
>                                            (piTac (useOp descOp [ use d done
>                                                                 , muTac (use d done) ] done)
>                                                   (\v ->
>                                                    bp @@@ [conTac $ use v done]))))
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
>     , opTy = sOpTy
>     , opRun = sOpRun
>     } where
>         sOpTy chev [e , b, x] = do
>           (e :=>: ev) <- chev (enumU :>: e)
>           (b :=>: bv) <- chev (branchesOp @@ [ev , L (K desc) ] :>: b)
>           (x :=>: xv) <- chev (ENUMT ev :>: x)
>           return $ ([ e :=>: ev
>                     , b :=>: bv
>                     , x :=>: xv ] 
>                     , desc)
>         sOpRun :: [VAL] -> Either NEU VAL
>         sOpRun [CONSE t e' , ps , ZE] = Right $ ps $$ Fst
>         sOpRun [CONSE t e' , ps , SU n] = Right $
>           switchDOp @@ [ e' 
>                        , ps $$ Snd
>                        , n ]
>         sOpRun [_ , _ , N n] = Left n
