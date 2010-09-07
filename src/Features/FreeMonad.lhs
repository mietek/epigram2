\section{FreeMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.FreeMonad where

%endif

> import -> CanConstructors where
>   Monad     :: t -> t -> Can t
>   Return    :: t -> Can t
>   Composite :: t -> Can t

> import -> CanPats where
>   pattern MONAD d x   = C (Monad d x)
>   pattern RETURN x    = C (Return x)
>   pattern COMPOSITE t = C (Composite t)

> import -> CanDisplayPats where
>   pattern DMONAD d x = DC (Monad d x)
>   pattern DRETURN x  = DC (Return x)
>   pattern DCOMPOSITE t = DC (Composite t)


> import -> CanCompile where
>   makeBody (Return x)    = Tuple [CTag 0, makeBody x]
>   makeBody (Composite t) = Tuple [CTag 1, makeBody t]

> import -> CanTraverse where
>   traverse f (Monad d x)   = (| Monad (f d) (f x) |)
>   traverse f (Return x)    = (| Return (f x) |)
>   traverse f (Composite x) = (| Composite (f x) |)

> import -> CanHalfZip where
>   halfZip (Monad d1 x1) (Monad d2 x2) = Just (Monad (d1, d2) (x1, x2))
>   halfZip (Return x) (Return y) = Just (Return (x, y))
>   halfZip (Composite x) (Composite y) = Just (Composite (x, y))

> import -> CanPretty where
>   pretty (Monad d x)   = wrapDoc
>       (kword KwMonad <+> pretty d ArgSize <+> pretty x ArgSize)
>       ArgSize
>   pretty (Return x)    = wrapDoc
>       (kword KwReturn <+> pretty x ArgSize)
>       ArgSize
>   pretty (Composite x) = wrapDoc
>       (kword KwCon <+> pretty x ArgSize)
>       ArgSize

> import -> Pretty where

> import -> CanTyRules where
>   canTy chev (Set :>: Monad d x) = do
>     ddv@(d :=>: dv) <- chev (desc :>: d)
>     xxv@(x :=>: xv) <- chev (SET :>: x)
>     return $ Monad ddv xxv
>   canTy chev (Monad d x :>: Return v) = do
>     vvv@(v :=>: vv) <- chev (x :>: v)
>     return $ Return vvv
>   canTy chev (Monad d x :>: Composite y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [d, MONAD d x] :>: y)
>     return $ Composite yyv

> import -> OpCode where
>   substMonadOp = Op
>     { opName = "substMonad"
>     , opArity = 5
>     , opTyTel =  "D" :<: desc                  :-: \ dD ->
>                  "X" :<: SET                   :-: \ xX ->
>                  "Y" :<: SET                   :-: \ yY ->
>                  "f" :<: ARR xX (MONAD dD yY)  :-: \ f ->
>                  "t" :<: MONAD dD xX           :-: \ t ->
>                  Target $ MONAD dD yY
>     , opRun = substMonadOpRun
>     , opSimp = substMonadOpSimp
>     } where
>       substMonadOpRun :: [VAL] -> Either NEU VAL
>       substMonadOpRun [dD, xX, yY, f, COMPOSITE ts] = Right . COMPOSITE $
>         mapOp @@ [  dD, MONAD dD xX, MONAD dD yY,
>                     L $ "t" :. [.t. N $
>                     substMonadOp :@ [  dD -$ [], xX -$ [], yY -$ []
>                                     ,  f -$ [], NV t] ] ,
>                     ts]
>       substMonadOpRun [d, x, y, f, RETURN z]  = Right $ f $$ A z
>       substMonadOpRun [d, x, y, f, N t]    = Left t
>
>       substMonadOpSimp :: Alternative m => [VAL] -> NameSupply -> m NEU
>       substMonadOpSimp [d, x, y, f, N t] r
>         | equal (SET :>: (x, y)) r &&
>           equal (ARR x (MONAD d x) :>: (f, ret)) r = pure t
>         where
>           ret = L ("x" :. [.x. RETURN (NV x)])
>       substMonadOpSimp [d, y, z, f, N (sOp :@ [_, x, _, g, N t])] r
>         | sOp == substMonadOp = pure $ substMonadOp :@ [d, x, z, comp, N t]
>         where  comp = L $ "x" :. [.x. N $
>                         substMonadOp :@ [ d -$ [], y -$ [], z -$ []
>                                         , f -$ [], g -$ [ NV x ] ] ]
>       substMonadOpSimp _ _ = empty

>   elimMonadOp :: Op
>   elimMonadOp = Op
>     { opName = "elimMonad"
>     , opArity = 6
>     , opTyTel =  "D" :<: desc                       :-: \ dD ->
>                  "X" :<: SET                        :-: \ xX ->
>                  "t" :<: MONAD dD xX                :-: \ t ->
>                  "P" :<: ARR (MONAD dD xX) SET      :-: \ pP ->
>                  "c" :<: (PI (descOp @@ [dD, MONAD dD xX]) $ L $ "ts" :. [.ts.
>                            ARR (N (boxOp :@ [  dD -$ []
>                                             ,  MONAD (dD -$ []) (xX -$ [])
>                                             ,  pP -$ [] , NV ts])) 
>                             (pP -$ [COMPOSITE (NV ts) ])])  :-: \ _ ->
>                  "v" :<: (PI xX $ L $ "x" :. [.x. pP -$ [ RETURN (NV x) ] ])       :-: \ _ ->
>                  Target $ pP $$ A t
>     , opRun = elimMonadOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimMonadOpRun :: [VAL] -> Either NEU VAL
>       elimMonadOpRun [d,x,COMPOSITE ts,bp,mc,mv] = Right $ 
>         mc $$ A ts $$ A (mapBoxOp @@ [d, MONAD d x, bp,
>           L $ "t" :. [.t. N $ elimMonadOp :@ [  d -$ [], x -$ []
>                                              ,  NV t , bp -$ []
>                                              ,  mc -$ [], mv -$ [] ] ] ,
>           ts])
>       elimMonadOpRun [d,x,RETURN z,bp,mc,mv] = Right $ mv $$ A z
>       elimMonadOpRun [_,_,N n,_,_,_] = Left n

> import -> Operators where
>   substMonadOp :
>   elimMonadOp :

> import -> OpCompile where
>   ("substMonad", [d, x, y, f, t]) -> App (Var "__substMonad") [d, f, t]
>   ("elimMonad", [d, x, v, p, mc, mv]) -> App (Var "__elimMonad") [d, mv, mc, v]

\question{What should the coercion rule be for |COMPOSITE|?}

> import -> Coerce where
>   coerce (Monad (d1, d2) (x1, x2)) q (RETURN v) =
>     Right . RETURN $ coe @@ [x1, x2, CON (q $$ Snd), v]
>   coerce (Monad (d1, d2) (x1, x2)) q (COMPOSITE y) =
>     Right . COMPOSITE $ coe @@ [
>         descOp @@ [d1, MONAD d1 x1],
>         descOp @@ [d2, MONAD d2 x2],
>         error "FreeMonad.coerce: missing equality proof",
>         y
>       ]


> import -> KeywordConstructors where
>   KwMonad   :: Keyword
>   KwReturn  :: Keyword

> import -> KeywordTable where
>   key KwMonad     = "Monad"
>   key KwReturn    = "`"  -- rename me

> import -> DInTmParsersSpecial where
>   (ArgSize, (|DRETURN (%keyword KwReturn%) (sizedDInTm ArgSize)|)) :
>   (AndSize, (|DMONAD (%keyword KwMonad%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :
