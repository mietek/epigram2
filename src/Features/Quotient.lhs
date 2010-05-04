\section{Quotients}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Quotient where

%endif

> import -> CanConstructors where
>   Quotient :: t -> t -> t -> Can t

> import -> CanTraverse where
>   traverse f (Quotient x r p) = (| Quotient (f x) (f r) (f p) |)

> import -> CanHalfZip where
>   halfZip (Quotient x r p) (Quotient y s q) = Just (Quotient (x, y) (r, s) (p, q))

> import -> Primitives where

> import -> CanPats where
>   pattern QUOTIENT x r p = C (Quotient x r p)
>   pattern CLASS x        = C (Con x)

> import -> CanDisplayPats where
>   pattern DQUOTIENT x r p = DC (Quotient x r p)
>   pattern DCLASS x        = DC (Con x)

> import -> CanPretty where
>   pretty (Quotient x r p) = wrapDoc
>       (sep [ kword KwQuotient
>            , nest 2 $ fsep $ map (flip pretty ArgSize) [x,r,p]
>            ])
>       ArgSize

|equivalenceRelation A R| is the proposition that |R| is an equivalence
relation over |A|.

> import -> QuotientDefinitions where
>   equivalenceRelation :: VAL -> VAL -> VAL
>   equivalenceRelation a r =
>     -- refl
>     AND (allty $ "x" :<: a :-: \x -> Target $ x =~ x) $
>     -- sym
>     AND (allty $ "x" :<: a :-: \x ->
>                  "y" :<: a :-: \y ->
>                  Target $ IMP (x =~ y) (y =~ x)
>         ) $
>     -- trans
>         (allty $ "x" :<: a :-: \x ->
>                  "y" :<: a :-: \y ->
>                  "z" :<: a :-: \z ->
>                  Target $ IMP (x =~ y) (IMP (y =~ z) (x =~ z))
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
>   qElimOp :

> import -> OpCompile where
>   ("elimQuotient", [_, _, _, z, _, m, _]) -> App m [z]

> import -> OpCode where
>   qElimOp = Op
>     { opName  = "elimQuotient"
>     , opArity = 7
>     , opTyTel = "X" :<: SET                             :-: \_X ->
>                 "R" :<: ARR _X (ARR _X PROP)            :-: \_R ->
>                 "p" :<: PRF (equivalenceRelation _X _R) :-: \p ->
>                 "z" :<: QUOTIENT _X _R p                :-: \z ->
>                 "P" :<: ARR (QUOTIENT _X _R p) SET      :-: \_P ->
>                 "m" :<: pity ("x" :<: _X :-: \x -> Target $ _P $$ A (CLASS x))
>                                                         :-: \m ->
>                 "h" :<: PRF (allty ("x" :<: _X :-: \x ->
>                                     "y" :<: _X :-: \y ->
>                                     Target $ IMP (_R $$ A x $$ A y)
>                                               (EQBLUE (_P $$ A (CLASS x) :>: m $$ A x)
>                                                       (_P $$ A (CLASS y) :>: m $$ A y))
>                                    ))                   :-: \_ ->
>                 Target $ _P $$ A z
>     , opRun = run
>     , opSimp = \_ _ -> empty
>     } where
>       run :: [VAL] -> Either NEU VAL
>       run [_, _, _, CLASS x, _, m, _] = Right (m $$ A x)
>       run [_, _, _, N n, _, _, _]     = Left n


> import -> OpRunEqGreen where
>   opRunEqGreen [QUOTIENT a r _, CLASS x, QUOTIENT b s _, CLASS y] =
>     Right $ ALL b . L . HF "x2" $ \x2 ->
>               IMP (EQBLUE (a :>: x) (b :>: x2))
>                   (s $$ A x2 $$ A y)
>   opRunEqGreen [QUOTIENT a r _, N x, QUOTIENT b s _, _]   = Left x
>   opRunEqGreen [QUOTIENT a r _, _,   QUOTIENT b s _, N y] = Left y

> import -> Coerce where
>   coerce (Quotient (_X, _Y) _ _) q (CLASS x) = Right $
>     CLASS (coe @@ [_X, _Y, CON $ q $$ Fst, x])


As a bit of syntactic sugar, we elaborate |con| as |COMPOSITE| and |[x]| as
|CLASS x|. \question{Why not just use |CON| rather than |COMPOSITE| everywhere?}

> import -> MakeElabRules where
>   makeElab' loc (MONAD d x :>: DCON t) =
>     makeElab' loc (MONAD d x :>: DCOMPOSITE t)
>   makeElab' loc (QUOTIENT a r p :>: DPAIR x DVOID) =
>     makeElab' loc (QUOTIENT a r p :>: DCLASS x)
