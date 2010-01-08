\section{Quotients}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Quotient where

> import -> CanConstructors where
>   Quotient :: t -> t -> t -> Can t

> import -> TraverseCan where
>   traverse f (Quotient x r p) = (| Quotient (f x) (f r) (f p) |)

> import -> HalfZipCan where
>   halfZip (Quotient x r p) (Quotient y s q) = Just (Quotient (x, y) (r, s) (p, q))

> import -> Primitives where

> import -> CanPats where
>   pattern QUOTIENT x r p = C (Quotient x r p)
>   pattern CLASS x        = C (Con x)

> import -> DisplayCanPats where
>   pattern DQUOTIENT x r p = DC (Quotient x r p)
>   pattern DCLASS x        = DC (Con x)

> import -> SugarTactics where

> import -> CanPretty where
>   pretty (Quotient x r p) =
>     parens (sep [ text "Quotient"
>                 , nest 2 $ fsep $ map pretty [x,r,p]
>                 ])

|equivalenceRelation A R| is the proposition that |R| is an equivalence
relation over |A|.

> import -> QuotientDefinitions where
>   equivalenceRelation :: VAL -> VAL -> VAL
>   equivalenceRelation a r =
>     -- refl
>     AND (allty $ "x" :<: a :-: \x -> Ret $ x =~ x) $
>     -- sym
>     AND (allty $ "x" :<: a :-: \x ->
>                  "y" :<: a :-: \y ->
>                  Ret $ IMP (x =~ y) (y =~ x)
>         ) $
>     -- trans
>         (allty $ "x" :<: a :-: \x ->
>                  "y" :<: a :-: \y ->
>                  "z" :<: a :-: \z ->
>                  Ret $ IMP (x =~ y) (IMP (y =~ z) (x =~ z))
>         )
>     where
>       x =~ y = r $$ A x $$ A y

> import -> CanTyRules where
>   canTy chev (Set :>: Quotient x r p) = do
>     x@(_ :=>: xv) <- chev (SET :>: x)
>     r@(_ :=>: rv) <- chev (ARR xv (ARR xv PROP) :>: r)
>     p@(_ :=>: _ ) <- chev (PRF (equivalenceRelation xv rv) :>: p)
>     return $ Quotient x r p
>
>   canTy chev (Quotient a r p :>: Con x) = do
>     x <- chev (a :>: x)
>     return $ Con x

> import -> Operators where
> import -> OpCompile where
> import -> OpCode where

> import -> OpRunEqGreen where
>   opRunEqGreen [QUOTIENT a r _, CLASS x, QUOTIENT b s _, CLASS y] =
>     Right $ ALL b . L . HF "x2" $ \x2 ->
>               IMP (EQBLUE (a :>: x) (b :>: x2))
>                   (s $$ A x2 $$ A y)
>   opRunEqGreen [QUOTIENT a r _, N x, QUOTIENT b s _, _]   = Left x
>   opRunEqGreen [QUOTIENT a r _, _,   QUOTIENT b s _, N y] = Left y

%endif

