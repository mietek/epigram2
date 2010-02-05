\section{Desc}
\label{sec:desc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Desc where

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

> import -> CanTraverse where
>   traverse f (Mu l) = (|Mu (traverse f l)|)

> import -> CanHalfZip where
>   halfZip (Mu t0) (Mu t1) = (| Mu (halfZip t0 t1) |)

> import -> BootstrapDesc where
>   inDesc :: VAL
>   inDesc = ARGF constructors (evTm cases)
>       where constructors = (CONSE (TAG "done")
>                             (CONSE (TAG "arg")
>                              (CONSE (TAG "argf")
>                               (CONSE (TAG "ind")
>                                (CONSE (TAG "ind1")
>                                 NILE)))))
>             cases = PAIR DONE 
>                     (PAIR (ARG SET (L $ "" :. [.s. IND (NV s) DONE]))
>                      (PAIR (ARG (NP enumREF) (L $ "" :. [.e. ARG (N (branchesDOp :@ [NV e])) (L $ "" :. [.t. DONE])]))
>                       (PAIR (ARG SET (L $ "" :. [.h. IND1 DONE]))
>                        (PAIR (IND1 DONE)
>                         VOID))))
>   descFakeREF :: REF
>   descFakeREF = [("Primitive", 0), ("Desc", 0)] := (FAKE :<: SET)
>   desc :: VAL
>   desc = MU (Just (N (P descFakeREF))) inDesc
>
>   descREF :: REF
>   descREF = [("Primitive", 0), ("Desc", 0)] := (DEFN desc :<: SET)

>   descDREF :: REF
>   descDREF = [("Primitive", 0), ("DescD", 0)] := (DEFN inDesc :<: desc)

> import -> Primitives where
>   ("Desc", descREF) :
>   ("DescD", descDREF) :

> import -> CanPats where
>   pattern MU l x  = C (Mu (l :?=: Id x))
>   pattern DONE = CON (PAIR ZE VOID)
>   pattern ARG s d = CON (PAIR (SU ZE) (PAIR s (PAIR d VOID)))
>   pattern ARGF s d = CON (PAIR (SU (SU ZE)) (PAIR s (PAIR d VOID)))
>   pattern IND h d = CON (PAIR (SU (SU (SU ZE))) (PAIR h (PAIR d VOID)))
>   pattern IND1 d = CON (PAIR (SU (SU (SU (SU ZE)))) (PAIR d VOID))

> import -> CanDisplayPats where
>   pattern DMU l x  = DC (Mu (l :?=: Id x))
>   pattern DDONE = DCON (DPAIR DZE DVOID)
>   pattern DARG s d = DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR d DVOID)))
>   pattern DARGF s d = DCON (DPAIR (DSU (DSU DZE)) (DPAIR s (DPAIR d DVOID)))
>   pattern DIND h d = DCON (DPAIR (DSU (DSU (DSU DZE))) (DPAIR h (DPAIR d DVOID)))
>   pattern DIND1 d = DCON (DPAIR (DSU (DSU (DSU (DSU DZE)))) (DPAIR d DVOID))

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

> import -> Coerce where
>   -- coerce :: (Can (VAL,VAL)) -> VAL -> VAL -> Either NEU VAL
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



> import -> ElimTyRules where
>   elimTy chev (_ :<: t@(Mu (_ :?=: Id d))) Out = return (Out, descOp @@ [d , C t])


> import -> Operators where
>   descOp :
>   boxOp :
>   mapBoxOp :
>   elimOp :
>   mapOp :

> import -> OpCompile where
>   ("fold", [d,v,bp,p]) -> App (Var "__fold") [d, p, v]
>   ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   ("map", [d,a,b,f,x]) -> App (Var "__map") [d, f, x]

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
>       dOpRun [DONE,xX]    = Right UNIT
>       dOpRun [ARG aA dD,xX] = Right $
>              SIGMA aA . L $ HF "a" $ \a ->
>                descOp @@ [dD $$ A a,xX]
>       dOpRun [ARGF aA dD,xX] = Right $
>              SIGMA (ENUMT aA) . L $ HF "a" $ \a ->
>                descOp @@ [switchOp @@ [aA, a, L (K desc), dD],xX]
>       dOpRun [IND hH dD,xX] = Right (TIMES (ARR hH xX) (descOp @@ [dD,xX]))
>       dOpRun [IND1 dD,xX] = Right (TIMES xX (descOp @@ [dD,xX]))
>       dOpRun [N dD,_]     = Left dD


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
>       boxOpRun [DONE   ,_,_,_] = Right UNIT
>       boxOpRun [ARG aA dD,xX,pP,v] = Right $ 
>         boxOp @@ [ dD $$ A (v $$ Fst) , xX , pP , v $$ Snd ] 
>       boxOpRun [ARGF aA dD,xX,pP,v] = Right $ 
>         boxOp @@ [ switchOp @@ [aA, v $$ Fst, L (K desc), dD] , xX , pP , v $$ Snd ] 
>       boxOpRun [IND hH dD,xX,pP,v] = Right $ 
>         TIMES (PI hH (L $ HF "h" $ \h -> pP $$ A (v $$ Fst $$ A h))) 
>               (boxOp @@ [dD, xX, pP, v $$ Snd])
>       boxOpRun [IND1 dD,xX,pP,v] = Right $ 
>         TIMES (pP $$ A (v $$ Fst)) (boxOp @@ [dD, xX, pP, v $$ Snd]) 
>       boxOpRun [N x    ,_,_,_] = Left x


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
>       mapBoxOpRun [DONE,xX,pP,p,v] = Right VOID
>       mapBoxOpRun [ARG aA dD,xX,pP,p,v] = Right $ 
>         mapBoxOp @@ [dD $$ A (v $$ Fst), xX, pP, p, v $$ Snd]  
>       mapBoxOpRun [ARGF aA dD,xX,pP,p,v] = Right $ 
>         mapBoxOp @@ [switchOp @@ [aA, v $$ Fst, L (K desc), dD], xX, pP, p, v $$ Snd]  
>       mapBoxOpRun [IND hH dD,xX,pP,p,v] = Right $ 
>         PAIR (PI hH (L $ HF "h" $ \h -> p $$ A (v $$ Fst $$ A h))) 
>              (mapBoxOp @@ [dD, xX, pP, p, v $$ Snd])
>       mapBoxOpRun [IND1 dD,xX,pP,p,v] = Right $ 
>         PAIR (p $$ A (v $$ Fst)) 
>              (mapBoxOp @@ [dD, xX, pP, p, v $$ Snd])
>       mapBoxOpRun [N x    ,_, _,_,_] = Left x

>   elimOpMethodType = L . HF "d" $ \d ->
>                      L . HF "P" $ \_P ->
>                      PI (descOp @@ [d, MU Nothing d])
>                         (L . HF "x" $ \x ->
>                          ARR (boxOp @@ [d, MU Nothing d, _P, x])
>                              (_P $$ A (CON x)))

>   elimOpLabMethodType = L . HF "l" $ \l ->
>                         L . HF "d" $ \d ->
>                         L . HF "P" $ \_P ->
>                         PI (descOp @@ [d, MU (Just l) d])
>                            (L . HF "x" $ \x ->
>                             ARR (boxOp @@ [d, MU (Just l) d, _P, x])
>                                 (_P $$ A (CON x)))

>   elimOp :: Op
>   elimOp = Op
>     { opName = "fold"
>     , opArity = 4
>     , opTyTel = elimOpTy
>     , opRun = elimOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimOpTy = 
>         "D" :<: desc :-: \dD ->
>         "v" :<: MU Nothing dD :-: \v ->
>         "P" :<: (ARR (MU Nothing dD) SET) :-: \pP ->
>         "p" :<: (elimOpMethodType $$ A dD $$ A pP) :-: \p ->
>         Target (pP $$ A v)
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [dD,CON v,pP,p] = Right $ 
>         p $$ A v $$ A (mapBoxOp @@ [ dD , MU Nothing dD , pP
>                                    , L $ HF "w" $ \w -> 
>                                        elimOp @@ [ dD , w , pP , p ]
>                                    , v]) 
>       elimOpRun [_,N x, _,_] = Left x


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
>         bOpRun [NILE ] = Right UNIT
>         bOpRun [CONSE t e' ] = 
>           Right (TIMES desc 
>                 (branchesDOp @@ [e']))
>         bOpRun [N e] = Left e 

>   mapOp = Op
>     { opName  = "map"
>     , opArity = 5
>     , opTyTel    = mapOpTy
>     , opRun   = mapOpRun
>     , opSimp  = mapOpSimp
>     } where
>         mapOpTy = 
>           "dD" :<: desc :-: \dD -> 
>           "xX" :<: SET :-: \xX ->
>           "yY" :<: SET :-: \yY ->
>           "f" :<: ARR xX yY :-: \f ->
>           "v" :<: (descOp @@ [dD, xX]) :-: \v -> 
>           Target (descOp @@ [dD, yY])
>
>         mapOpRun :: [VAL] -> Either NEU VAL
>         mapOpRun [DONE,    _, _, _, _] = Right VOID
>         mapOpRun [ARG aA dD, xX, yY, f, v] = Right $
>           PAIR (v $$ Fst)
>                (mapOp @@ [ dD $$ A (v $$ Fst), xX, yY, f, v $$ Snd])
>         mapOpRun [ARGF aA dD, xX, yY, f, v] = Right $
>           PAIR (v $$ Fst)
>                (mapOp @@ [switchOp @@ [aA, v $$ Fst, L (K desc), dD], xX, yY, f, v $$ Snd])
>         mapOpRun [IND hH dD, xX, yY, f, v] = Right $
>           PAIR (L $ HF "h" $ \h -> f $$ A (v $$ Fst $$ A h))
>                (mapOp @@ [ dD, xX, yY, f, v $$ Snd])
>         mapOpRun [IND1 dD, xX, yY, f, v] = Right $
>           PAIR (f $$ A (v $$ Fst))
>                (mapOp @@ [dD, xX, yY, f, v $$ Snd])
>         mapOpRun [N d,     a, b, f, x] = Left d
>
>         mapOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>         mapOpSimp [dD, xX, yY, f, N v] r
>           | equal (ARR xX yY :>: (f, identity)) r = pure v
>           where
>             identity = L (HF "x" $ \x -> x)
>         mapOpSimp [dD, _, zZ, f, N (mOp :@ [_, xX, _, g, N v])] r
>           | mOp == mapOp = mapOpSimp args r <|> pure (mapOp :@ args)
>           where
>             comp f g = L (HF "x" $ \x -> f $$ A (g $$ A x))
>             args = [dD, xX, zZ, comp f g, N v]
>         mapOpSimp _ _ = empty



As some useful syntactic sugar, we let inductive types elaborate
lists (so |[]| becomes |@[0]| and |[s , t]| becomes |@ [1 s t]|).

> import -> ElaborateRules where
>     elaborate b (MU l d :>: DVOID) =
>         elaborate b (MU l d :>: DCON (DPAIR DZE DVOID))
>     elaborate b (MU l d :>: DPAIR s t) =
>         elaborate b (MU l d :>: DCON (DPAIR (DSU DZE) (DPAIR s (DPAIR t DVOID))))
>     elaborate True (SET :>: DMU Nothing d) = do
>         GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>         let fr = nom := FAKE :<: ty
>         xs <- (| boySpine getAuncles |)
>         let lt = N (P fr $:$ xs)
>         let lv = evTm lt
>         (t :=>: v) <- elaborate False (desc :>: d)
>         return (MU (Just lt) t :=>: MU (Just lv) v)

To avoid an infinite loop when distilling, we have to be a little cleverer
and call canTy directly rather than letting distill do it for us.

> import -> DistillRules where
>     distill _ (MU _ _ :>: CON (PAIR ZE VOID)) =
>         return (DVOID :=>: CON (PAIR ZE VOID))
>     distill es (C ty@(Mu _) :>: C c@(Con (PAIR (SU ZE) (PAIR _ (PAIR _ VOID))))) = do
>         Con (DPAIR _ (DPAIR s (DPAIR t _)) :=>: v) <- canTy (distill es) (ty :>: c)
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
