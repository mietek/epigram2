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

> import -> DisplayCanPats where
>   pattern DMONAD d x = DC (Monad d x)
>   pattern DRETURN x  = DC (Return x)
>   pattern DCOMPOSITE t = DC (Composite t)


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
>   substOp = Op
>     { opName = "subst"
>     , opArity = 5
>     , opTyTel =  "D" :<: desc                  :-: \ dD ->
>                  "X" :<: SET                   :-: \ xX ->
>                  "Y" :<: SET                   :-: \ yY ->
>                  "f" :<: ARR xX (MONAD dD yY)  :-: \ f ->
>                  "t" :<: MONAD dD xX           :-: \ t ->
>                  Ret $ MONAD dD yY
>     , opRun = substOpRun
>     , opSimp = substOpSimp
>     } where
>       substOpRun :: [VAL] -> Either NEU VAL
>       substOpRun [dD, xX, yY, f, COMPOSITE ts] = Right . COMPOSITE $
>         mapOp @@ [  dD, MONAD dD xX, MONAD dD yY,
>                     L . HF "t" $ \ t ->
>                     substOp @@ [dD, xX, yY, f, t],
>                     ts]
>       substOpRun [d, x, y, f, RETURN z]  = Right $ f $$ A z
>       substOpRun [d, x, y, f, N t]    = Left t
>
>       substOpSimp :: Alternative m => [VAL] -> Root -> m NEU
>       substOpSimp [d, x, y, f, N t] r
>         | equal (SET :>: (x, y)) r &&
>           equal (ARR x (MONAD d x) :>: (f, ret)) r = pure t
>         where
>           ret = eval (L ("x" :. [.x. RETURN (NV x)])) B0
>       substOpSimp [d, y, z, f, N (sOp :@ [_, x, _, g, N t])] r
>         | sOp == substOp = pure $ substOp :@ [d, x, z, comp, N t]
>         where  comp = L . HF "x" $ \ x -> substOp @@ [d, y, z, f, g $$ A x]
>       substOpSimp _ _ = empty

>   elimMonadOp :: Op
>   elimMonadOp = Op
>     { opName = "elimMonad"
>     , opArity = 6
>     , opTyTel =  "D" :<: desc                       :-: \ dD ->
>                  "X" :<: SET                        :-: \ xX ->
>                  "t" :<: MONAD dD xX                :-: \ t ->
>                  "P" :<: ARR (MONAD dD xX) SET      :-: \ pP ->
>                  "c" :<: (pity $
>                     "ts" :<: descOp @@ [dD, MONAD dD xX]         :-: \ ts ->
>                     "hs" :<: boxOp @@ [dD, MONAD dD xX, pP, ts]  :-: \ _ ->
>                      Ret $ pP $$ A (COMPOSITE ts))  :-: \ _ ->
>                  "v" :<: (pity $
>                     "x" :<: xX :-: \ x ->
>                     Ret $ pP $$ A (RETURN x))       :-: \ _ ->
>                  Ret $ pP $$ A t
>     , opRun = elimMonadOpRun
>     , opSimp = \_ _ -> empty
>     } where
>       elimMonadOpRun :: [VAL] -> Either NEU VAL
>       elimMonadOpRun [d,x,COMPOSITE ts,bp,mc,mv] = Right $ 
>         mc $$ A ts $$ A (mapBoxOp @@ [d, MONAD d x, bp,
>           L . HF "t" $ \ t -> elimMonadOp @@ [d, x, t, bp, mc, mv],
>           ts])
>       elimMonadOpRun [d,x,RETURN z,bp,mc,mv] = Right $ mv $$ A z
>       elimMonadOpRun [_,_,N n,_,_,_] = Left n

> import -> Operators where
>   substOp :
>   elimMonadOp :

> import -> OpCompile where
>   ("subst", [d, x, y, f, t]) -> App (Var "__subst") [d, f, t]
>   ("elimMonad", [d, x, v, p, mc, mv]) -> App (Var "__elimMonad") [d, mv, mc, v]

