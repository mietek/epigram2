\section{FreeMonad}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module FreeMonad where

%endif

> import -> CanConstructors where
>   Monad     :: t -> t -> Can t
>   Return    :: t -> Can t
>   Composite :: t -> Can t

> import -> CanPats where
>   pattern MONAD d x   = C (Monad d x)
>   pattern RETURN x    = C (Return x)
>   pattern COMPOSITE t = C (Composite t)

> import -> SugarTactics where

> import -> CanCompile where
>   makeBody (Return x)    = Tuple [CTag 0, makeBody x]
>   makeBody (Composite t) = Tuple [CTag 1, makeBody t]

> import -> TraverseCan where
>   traverse f (Monad d x)   = (| Monad (f d) (f x) |)
>   traverse f (Return x)    = (| Return (f x) |)
>   traverse f (Composite x) = (| Composite (f x) |)

> import -> HalfZipCan where
>   halfZip (Monad d1 x1) (Monad d2 x2) = Just (Monad (d1, d2) (x1, x2))
>   halfZip (Return x) (Return y) = Just (Return (x, y))
>   halfZip (Composite x) (Composite y) = Just (Composite (x, y))

> import -> CanPretty where
>   prettyCan (Monad d x)   = parens (text "Monad" <+> pretty d <+> pretty x)
>   prettyCan (Return x)    = parens (text "'" <+> pretty x)
>   prettyCan (Composite x) = parens (text "@" <+> pretty x)

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
>   substOp = Op
>     { opName = "subst"
>     , opArity = 5
>     , opTy = substOpTy
>     , opRun = substOpRun
>     } where
>       substOpTy chev [d, x, y, f, t] = do
>         dd@(d :=>: dv) <- chev (desc :>: d)
>         xx@(x :=>: xv) <- chev (SET :>: x)
>         yy@(y :=>: yv) <- chev (SET :>: y)
>         ff@(f :=>: fv) <- chev (ARR xv (MONAD dv yv) :>: f)
>         tt@(t :=>: tv) <- chev (MONAD dv xv :>: t)
>         return ([dd, xx, yy, ff, tt], MONAD dv yv)
>       substOpTy _ xs = throwError [ "subst: arity mismatch: " ++
>                                     show (length xs) ++ " should be 5" ]
>       substOpRun :: [VAL] -> Either NEU VAL
>       substOpRun [d, x, y, f, COMPOSITE ts] = Right $ eval
>         [.d.x.y.f.ts.
>           COMPOSITE . N $
>             mapOp :@ [ NV d, MONAD (NV d) (NV x), MONAD (NV d) (NV y)
>                      , L $ "t" :. [.t. N $ substOp :@ [NV d, NV x, NV y, NV f, NV t]]
>                      , NV ts ]
>         ] $ B0 :< d :< x :< y :< f :< ts
>       substOpRun [d, x, y, f, RETURN z]  = Right $ f $$ A z
>       substOpRun [d, x, y, f, N t]    = Left t

>   elimMonadOp :: Op
>   elimMonadOp = Op
>     { opName = "elimMonad"
>     , opArity = 6
>     , opTy = elimMonadOpTy
>     , opRun = elimMonadOpRun
>     } where
>       elimMonadOpTy chev [d,x,v,bp,mc,mv] = do
>         dd@(d :=>: dv)    <- chev (desc :>: d)
>         xx@(x :=>: xv)    <- chev (SET :>: x)
>         vvv@(v :=>: vv)   <- chev (MONAD dv xv :>: v)
>         bbp@(bp :=>: bpv) <- chev (ARR (MONAD dv xv) SET :>: bp)
>         mmc@(mc :=>: mcv) <- chev (elimMonadConMethodType dv (MONAD dv xv) bpv :>: mc)
>         mmv@(mv :=>: mvv) <- chev (elimMonadVarMethodType xv bpv :>: mv)
>         return ([ dd, xx, vvv, bbp, mmc, mmv ], bpv $$ A vv)
>
>       elimMonadConMethodType d r p = eval
>         [.d.r.p.
>          PI (N $ descOp :@ [NV d, NV r])
>             (L $ "x" :. [.x. ARR (N $ boxOp :@ [NV d, NV r, NV p, NV x])
>                                  (N $ V p :$ A (COMPOSITE (NV x)))
>                         ])
>         ] $ B0 :< d :< r :< p
>
>       elimMonadVarMethodType x p = eval
>         [.x.p.
>          PI (NV x) (L $ "z" :. [.z. N $ V p :$ A (RETURN (NV z))])
>         ] $ B0 :< x :< p
>
>       elimMonadOpRun :: [VAL] -> Either NEU VAL
>       elimMonadOpRun [d,x,COMPOSITE ts,bp,mc,mv] = Right $ eval
>         [.d.x.ts.bp.mc.mv.
>          N $ V mc
>           :$ A (NV ts)
>           :$ A (N $ mapBoxOp :@
>                     [ NV d, MONAD (NV d) (NV x), NV bp
>                     , L $ "t" :. [.t.
>                         N $ elimMonadOp :@
>                           [ NV d, NV x, NV t, NV bp, NV mc, NV mv ] ]
>                     , NV ts ])
>         ] $ B0 :< d :< x :< ts :< bp :< mc :< mv
>       elimMonadOpRun [d,x,RETURN z,bp,mc,mv] = Right $ eval
>         [.mv.z.
>          N $ V mv :$ A (NV z)
>         ] $ B0 :< mv :< z
>       elimMonadOpRun [_,_,N n,_,_,_] = Left n

> import -> Operators where
>   substOp :
>   elimMonadOp :

> import -> OpCompile where
>   ("subst", [d, x, y, f, t]) -> App (Var "__subst") [d, f, t]
>   ("elimMonad", [d, x, v, p, mc, mv]) -> App (Var "__elimMonad") [d, mv, mc, v]

