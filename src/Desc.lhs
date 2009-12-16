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
>   Desc   :: Can t
>   Mu     :: t -> Can t
>   Done   :: Can t
>   Arg    :: t -> t -> Can t
>   Ind    :: t -> t -> Can t
>   Ind1   :: t -> Can t

> import -> TraverseCan where
>   traverse _ Desc       = (|Desc|)
>   traverse f (Mu x)     = (|Mu (f x)|)
>   traverse _ Done       = (|Done|)
>   traverse f (Arg x y)  = (|Arg (f x) (f y)|)
>   traverse f (Ind x y)  = (|Ind (f x) (f y)|)
>   traverse f (Ind1 x)   = (|Ind1 (f x)|)

> import -> HalfZipCan where
>   halfZip Desc Desc = Just Desc
>   halfZip (Mu t0) (Mu t1) = Just (Mu (t0,t1))
>   halfZip Done Done = Just Done
>   halfZip (Arg s0 t0) (Arg s1 t1) = Just (Arg (s0,s1) (t0,t1))
>   halfZip (Ind s0 t0) (Ind s1 t1) = Just (Ind (s0,s1) (t0,t1))
>   halfZip (Ind1 s0) (Ind1 s1) = Just (Ind1 (s0,s1))

> import -> CanPats where
>   pattern DESC     = C Desc
>   pattern MU x     = C (Mu x)
>   pattern DONE     = C Done
>   pattern ARG x y  = C (Arg x y)
>   pattern IND x y  = C (Ind x y)
>   pattern IND1 x   = C (Ind1 x)

> import -> CanCompile where
>   makeBody Done = Tuple [CTag 0]
>   makeBody (Arg x y) = Tuple [CTag 1, makeBody y]
>   makeBody (Ind x y) = Tuple [CTag 2, makeBody y]
>   makeBody (Ind1 y) = Tuple [CTag 3, makeBody y]

> import -> SugarTactics where
>   descTac = can Desc
>   muTac t = can $ Mu t
>   doneTac = can Done
>   argTac h f = can $ Arg h (lambda f)
>   indTac x d = can $ Ind x d
>   ind1Tac d = can $ Ind1 d

> import -> CanPretty where
>   prettyCan Desc   = text "Desc"
>   prettyCan (Mu t) = parens (text "Mu" <+> pretty t)
>   prettyCan Done   = text "Done"
>   prettyCan (Arg t1 t2) = parens (text "Arg" <+> pretty t1 <+> pretty t2)
>   prettyCan (Ind t1 t2) = parens (text "Ind" <+> pretty t1 <+> pretty t2)
>   prettyCan (Ind1 t) = parens (text "Ind1" <+> pretty t)

> import -> CanTyRules where
>   canTy _ (Set :>: Desc)     = return Desc
>   canTy chev (Set :>: Mu x)     = do
>     xxv@(x :=>: xv) <- chev (DESC :>: x)
>     return $ Mu xxv
>   canTy _ (Desc :>: Done)    = return Done
>   canTy chev (Desc :>: Arg x y) = do
>     xxv@(x :=>: xv) <- chev (SET :>: x)
>     yyv@(y :=>: yv) <- chev (ARR xv DESC :>: y)
>     return $ Arg xxv yyv
>   canTy chev (Desc :>: Ind x y) = do
>     xxv@(x :=>: xv) <- chev (SET :>: x)
>     yyv@(y :=>: yv) <- chev (DESC :>: y)
>     return $ Ind xxv yyv
>   canTy chev (Desc :>: Ind1 x) = do
>     xxv@(x :=>: xv) <- chev (DESC :>: x)
>     return $ Ind1 xxv
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

> import -> OpCompile where
>   ("elimOp", [d,bp,p,v]) -> App (Var "__elim") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]

> import -> OpCode where
>   descOp :: Op
>   descOp = Op
>     { opName = "descOp"
>     , opArity = 2
>     , opTy = dOpTy
>     , opRun = dOpRun
>     } where
>       dOpTy chev [x,y] = do
>                  (x :=>: xv) <- chev (DESC :>: x)
>                  (y :=>: yv) <- chev (SET :>: y)
>                  return $ ([ x :=>: xv
>                            , y :=>: yv ]
>                           , SET)
>       dOpRun :: [VAL] -> Either NEU VAL
>       dOpRun [DONE,y]    = Right UNIT
>       dOpRun [ARG x y,z] = Right $ trustMe (opRunArgType :>: opRunArgTac) $$ A x $$ A y $$ A z
>       dOpRun [IND x y,z] = Right $ trustMe (opRunIndType :>: opRunIndTac) $$ A x $$ A y $$ A z
>       dOpRun [IND1 y,z] = Right $ trustMe (opRunInd1Type :>: opRunInd1Tac) $$ A y $$ A z
>       dOpRun [N x,_]     = Left x
>
>       opRunTypeTac arg = arrTac arg
>                                 (arrTac setTac
>                                         setTac)
>       opRunArgType = trustMe (SET :>: opRunArgTypeTac) 
>       opRunArgTypeTac = piTac setTac
>                               (\x ->
>                                opRunTypeTac (arrTac (use x done)
>                                                     descTac))
>       opRunArgTac = lambda $ \x ->
>                     lambda $ \f ->
>                     lambda $ \d ->
>                     sigmaTac (use x done)
>                              (\a ->
>                               useOp descOp [ f @@@ [use a done]
>                                            , use d done ] done)
>
>       opRunIndType = trustMe (SET :>: opRunIndTypeTac)
>       opRunIndTypeTac = arrTac (can Set) 
>                                (opRunTypeTac (can Desc))
>       opRunIndTac = lambda $ \h ->
>                     lambda $ \x ->
>                     lambda $ \d ->
>                     timesTac (arrTac (use h done)
>                                      (use d done))
>                              (useOp descOp [ use x done
>                                            , use d done ] done)
>
>       opRunInd1Type = trustMe (SET :>: opRunInd1TypeTac)
>       opRunInd1TypeTac = opRunTypeTac (can Desc)
>       opRunInd1Tac = lambda $ \x ->
>                      lambda $ \d ->
>                      timesTac (use d done)
>                               (useOp descOp [ use x done
>                                             , use d done ] done)




>   boxOp :: Op
>   boxOp = Op
>     { opName = "boxOp"
>     , opArity = 4
>     , opTy = boxOpTy
>     , opRun = boxOpRun
>     } where
>       boxOpTy chev [w,x,y,z] = do
>         (w :=>: wv) <- chev (DESC :>: w)
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
>       boxOpRun [ARG a f,d,p,v] = Right $ trustMe (opRunArgType :>: opRunArgTac) 
>                                          $$ A a $$ A f $$ A d $$ A p $$ A v
>       boxOpRun [IND h x,d,p,v] = Right $ trustMe (opRunIndType :>: opRunIndTac)
>                                          $$ A h $$ A x $$ A d $$ A p $$ A v
>       boxOpRun [IND1 x,d,p,v] = Right $ trustMe (opRunInd1Type :>: opRunInd1Tac)
>                                         $$ A x $$ A d $$ A p $$ A v
>       boxOpRun [N x    ,_,_,_] = Left x
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
>                                       opRunTypeTac (can $ Arg (use x done)
>                                                               (use f done))))
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
>           (x :=>: xv) <- chev (DESC :>: x)
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
>       mapBoxOpRun [ARG a f,d,bp,p,v] = Right $ trustMe (mapBoxArgType :>: mapBoxArgTac) 
>                                                $$ A a $$ A f $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [IND h x,d,bp,p,v] = Right $ trustMe (mapBoxIndType :>: mapBoxIndTac) 
>                                                $$ A h $$ A x $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [IND1 x,d,bp,p,v] = Right $ trustMe (mapBoxInd1Type :>: mapBoxInd1Tac) 
>                                                 $$ A x $$ A d $$ A bp $$ A p $$ A v
>       mapBoxOpRun [N x    ,_, _,_,_] = Left x
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
>                                        mapBoxTypeTac (can $ Arg (use a done)
>                                                                 (use f done))))
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
>       elimOpTy chev [d,bp,p,v] = do
>         (d :=>: dv) <- chev (DESC :>: d)
>         (bp :=>: bpv) <- chev (ARR (MU dv) SET :>: bp)
>         (v :=>: vv) <- chev (MU dv :>: v)
>         (p :=>: pv) <- chev (PI (descOp @@ [dv,MU dv]) 
>                     (eval [.d.bp.v. L $ "" :. [.x. 
>                         ARR (N (boxOp :@ [NV d,MU (NV d),NV bp,NV x]))
>                             (N (V bp :$ A (CON (NV x))))]
>                         ] $ B0 :< dv :< bpv :< vv) :>: p)
>         return ([ d :=>: dv
>                 , bp :=>: bpv
>                 , p :=>: pv
>                 , v :=>: vv ]
>                 , bpv $$ A vv)
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [d,bp,p,CON v] = Right $ trustMe (elimOpType :>: elimOpTac) 
>                                          $$ A d $$ A bp $$ A p $$ A v
>       elimOpRun [_, _,_,N x] = Left x
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
>                                                         , use bp done
>                                                         , use p done
>                                                         , use x done ] done 
>                                          , use v done ] done ]

