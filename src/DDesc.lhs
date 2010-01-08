\section{Desc}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module DDesc where

%endif

> import -> CanConstructors where
>   DDesc   :: t -> Can t
>   DMu     :: Labelled (Id :*: Id) t -> t -> Can t
>   DDone   :: t -> Can t
>   DArg    :: t -> t -> Can t
>   DInd1   :: t -> t -> Can t
>   DInd    :: t -> t -> t -> Can t

> import -> TraverseCan where
>   traverse f (DDesc i) = (|DDesc (f i)|)
>   traverse f (DMu l i) = (|DMu (traverse f l) (f i)|)
>   traverse f (DDone p) = (|DDone (f p)|)
>   traverse f (DArg a d) = (|DArg (f a) (f d)|)
>   traverse f (DInd1 x y) = (|DInd1 (f x) (f y)|)
>   traverse f (DInd x y z) = (|DInd (f x) (f y) (f z)|)

> import -> HalfZipCan where
>   halfZip (DDesc i0) (DDesc i1) = (|(DDesc (i0,i1))|)
>   halfZip (DMu l0 i0) (DMu l1 i1) = (|(\p -> DMu p (i0,i1)) (halfZip l0 l1)|)
>   halfZip (DDone p0) (DDone p1) = (|(DDone (p0,p1))|)
>   halfZip (DArg a0 d0) (DArg a1 d1) = (|(DArg (a0,a1) (d0,d1))|)
>   halfZip (DInd1 x0 y0) (DInd1 x1 y1) = (|(DInd1 (x0,x1) (y0,y1))|)
>   halfZip (DInd x0 y0 z0) (DInd x1 y1 z1) = (|(DInd (x0,x1) (y0,y1) (z0,z1))|)

> import -> CanPats where
>   pattern DDESC i = C (DDesc i)
>   pattern DMU l ii x i = C (DMu (l :?=: (Id ii :& Id x)) i) 
>   pattern DDONE p = C (DDone p) 
>   pattern DARG s d = C (DArg s d) 
>   pattern DIND h hi d = C (DInd h hi d) 
>   pattern DIND1 i d = C (DInd1 i d) 


> import -> SugarTactics where
>   dmuTac ii t i = can $ DMu (Nothing :?=: (Id ii :& Id t)) i
>   dmuTacL l i = can $ DMu l i
>   ddescTac i = can $ DDesc i 
>   ddoneTac p = can $ DDone p 
>   dargTac x y = can $ DArg x y 
>   dindTac x y z = can $ DInd x y z 
>   dind1Tac x y = can $ DInd1 x y 

> import -> CanTyRules where
>   canTy chev (Set :>: DMu (ml :?=: (Id ii :& Id x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (DDESC iiv) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ DMu (mlv :?=: (Id iiiiv :& Id xxv)) iiv
>   canTy chev (DMu tt@(_ :?=: (Id ii :& Id x)) i :>: Con y) = do
>     yyv <- chev (descOp @@ [ ii
>                            , x $$ A i 
>                            , L $ HF "i" $ \i -> C (DMu tt i)
>                            ] :>: y)
>     return $ Con yyv
>   canTy chev (Set :>: DDesc ii) = 
>     (|DDesc (chev (SET :>: ii))|)
>   canTy chev (DDesc ii :>: DDone p) =  
>     (|DDone (chev (PROP :>: p))|)
>   canTy chev (DDesc ii :>: DArg a d) = do
>     aav@(a :=>: av) <- chev (SET :>: a)  
>     ddv <- chev (ARR av (DDESC ii) :>: d)
>     (|(DArg aav ddv)|)  
>   canTy chev (DDesc ii :>: DInd1 i d) =
>     (|DInd1 (chev (ii :>: i)) (chev (DDESC ii :>: d))|)  
>   canTy chev (DDesc ii :>: DInd h hi d) = do
>     hhv@(h :=>: hv) <- chev (SET :>: h)
>     hihiv@(hi :=>: hiv) <- chev (ARR hv ii :>: hi)
>     ddv <- chev (DDESC ii :>: d)
>     (|(DInd hhv hihiv ddv)|)  

> import -> ElimTyRules where
>   elimTy chev (_ :<: (DMu tt@(_ :?=: (Id ii :& Id x)) i)) Out = 
>     return (Out, descOp @@ [ii , x $$ A i , L $ HF "i" $ \i -> C (DMu tt i)])

> import -> Operators where
>   ddescOp :
>   dboxOp :
>   dmapBoxOp :
>   delimOp :

> import -> OpCompile where
>   -- ("elimOp", [d,v,bp,p]) -> App (Var "__elim") [d, p, v]
>   -- ("mapBox", [x,d,bp,p,v]) -> App (Var "__mapBox") [x, p, v]
>   -- ("SwitchD", [e,b,x]) -> App (Var "__switch") [x, b]

> import -> OpCode where
>   ddescOp :: Op
>   ddescOp = Op
>     { opName = "ddescOp"
>     , opArity = 3
>     , opTyTel = ddOpTy
>     , opRun = ddOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       ddOpTy = 
>        "i" :<: SET :-: \i ->
>        "d" :<: DDESC i :-: \d ->
>        "x" :<: ARR i SET :-: \x ->
>        Ret SET
>       ddOpRun :: [VAL] -> Either NEU VAL
>       ddOpRun [ii,DDONE p,x]    = Right $ PRF p
>       ddOpRun [ii,DARG aa d,x] = Right $
>          eval [.ii.aa.d.x. 
>               SIGMA (NV aa) . L $ "" :. [.a.
>               (N (ddescOp :@ [NV ii,d $# [a],NV x]))
>               ]] $ B0 :< ii :< aa :< d :< x
>       ddOpRun [ii,DIND1 i d,x] = Right (TIMES (x $$ A i) (ddescOp @@ [ii,d,x]))
>       ddOpRun [ii,DIND h hi d,x] = 
>         Right (TIMES (PI h (L $ HF "h" (\h -> x $$ (A (hi $$ (A h)))))) 
>                      (ddescOp @@ [ii,d,x]))
>       ddOpRun [_,N x,_]     = Left x

>   dboxOp :: Op
>   dboxOp = Op
>     { opName = "dboxOp"
>     , opArity = 4
>     , opTyTel = dboxOpTy
>     , opRun = dboxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       dboxOpTy = 
>         "ii" :<: SET :-: \ii ->
>         "d" :<: DDESC ii :-: \d ->
>         "x" :<: ARR ii SET :-: \x ->
>         "v" :<: (descOp @@ [ii,d,x]) :-: \v ->
>         Ret $ DDESC (SIGMA ii (L $ HF "i" (\i -> x $$ A i)))
>       dboxOpRun :: [VAL] -> Either NEU VAL
>       dboxOpRun [ii,DDONE _ ,x,v] = Right (DDONE TRIVIAL)
>       dboxOpRun [ii,DARG a d,x,v] = Right $ 
>         dboxOp @@ [ii,d $$ (A (v $$ Fst)),x,v $$ Snd]
>       dboxOpRun [ii,DIND h hi d,x,v] = Right $
>         DIND h (L (HF "h" $ \hh -> PAIR (hi $$ A hh) (v $$ Fst $$ A hh))) 
>              (dboxOp @@ [ii,d,x,v $$ Snd])
>       dboxOpRun [ii,DIND1 i d,x,v] = Right $ 
>         DIND1 (PAIR i (v $$ Fst)) (dboxOp @@ [ii,d,x,v $$ Snd])
>       dboxOpRun [_,N x    ,_,_] = Left x

>   dmapBoxOp :: Op
>   dmapBoxOp = Op
>     { opName = "dmapBoxOp"
>     , opArity = 6
>     , opTyTel = mapBoxOpTy
>     , opRun = mapBoxOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       mapBoxOpTy = 
>         "ii" :<: SET :-: \ii ->
>         "d" :<: DDESC ii :-: \d ->
>         "x" :<: ARR ii SET :-: \x ->
>         let sigiix = SIGMA ii (L (HF "i" $ \i -> x $$ A i)) in
>           "bp" :<: ARR sigiix SET :-: \bp ->
>           "p" :<: (PI sigiix (L (HF "t" $ \t -> bp $$ A t))) :-: \p ->
>           "v" :<: (ddescOp @@ [ii,d,x]) :-: \v ->
>           Ret $ ddescOp @@ [sigiix,dboxOp @@ [ii,d,x,v],bp]
>       mapBoxOpRun :: [VAL] -> Either NEU VAL
>       mapBoxOpRun [DDONE _,x,bp,p,v] = Right VOID
>       mapBoxOpRun [DARG a d,x,bp,p,v] = Right $ 
>         dmapBoxOp @@ [d $$ (A (v $$ Fst)),x,bp,p,v $$ Snd]
>       mapBoxOpRun [DIND h hi d,x,bp,p,v] = Right $ 
>         PAIR (L (HF "x" $ \x -> p $$ A (PAIR (hi $$ A x) (v $$ Fst $$ A x)))) 
>              (dmapBoxOp @@ [d,x,bp,p,v $$ Snd]) 
>       mapBoxOpRun [DIND1 i d,x,bp,p,v] = Right $ 
>         PAIR (p $$ A (PAIR i (v $$ Fst))) (dmapBoxOp @@ [d,x,bp,p,v $$ Snd]) 
>       mapBoxOpRun [N d    ,_, _,_,_] = Left d

>   delimOp :: Op
>   delimOp = Op
>     { opName = "delimOp"
>     , opArity = 6
>     , opTyTel = elimOpTy
>     , opRun = elimOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimOpTy = 
>         "ii" :<: SET :-: \ii ->
>         "d" :<: (ARR ii (DDESC ii)) :-: \d ->
>         "i" :<: ii :-: \i ->
>         "v" :<: (DMU Nothing ii d i) :-: \v ->
>         "bp" :<: (ARR (SIGMA ii (L (HF "i'" $ \i' -> DMU Nothing ii d i')))
>                       SET) 
>                    :-: \bp ->
>         "m" :<: 
>           (pity ("i'" :<: ii :-: \i' ->
>                  "x" :<: (ddescOp @@ 
>                            [ ii , d $$ A i'
>                            , L $ HF "i''" $ \i'' -> DMU Nothing ii d i''
>                            ]) :-: \x ->
>                  "hs" :<: (ddescOp @@ 
>                             [ SIGMA ii (L $ HF "i" $ \i -> DMU Nothing ii d i) 
>                             , dboxOp @@
>                                  [ ii , d $$ A i'
>                                  , L $ HF "i''" $ \i'' -> DMU Nothing ii d i''
>                                  , x
>                                  ]
>                             , bp 
>                             ]) :-: \hs ->
>                  Ret (bp $$ A (PAIR i' (CON x))))) :-: \m ->
>          Ret (bp $$ A (PAIR i v))
>       elimOpRun :: [VAL] -> Either NEU VAL
>       elimOpRun [ii,d,i,CON x,bp,m] = Right $ 
>         m $$ A i $$ A x 
>           $$ A (dmapBoxOp @@ 
>                   [ ii , d $$ A i , L $ HF "i'" $ \i' -> DMU Nothing ii d i'
>                   , bp , L $ HF "t" $ \t -> 
>                            elimOp @@ [ii,d,t $$ Fst,t $$ Snd,bp,m] 
>                   , x
>                   ])
>       elimOpRun [_,N x, _,_] = Left x

