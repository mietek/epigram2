\section{Enum}
\label{sec:Features.Enum}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Enum where

%endif


> import -> RulesCode where

>   enumConstructors :: Tm {In, p} x
>   enumConstructors = CONSE (TAG "nil") (CONSE (TAG "cons") NILE)

>   enumBranches :: Tm {In, p} x
>   enumBranches =
>       PAIR (CONSTD UNIT)
>           (PAIR (SIGMAD UID (L $ "t" :. (PRODD (TAG "E") IDD (CONSTD UNIT))))
>               VOID)

>   enumD :: Tm {In, p} x
>   enumD = SIGMAD  (ENUMT enumConstructors)
>                     (L $ "c" :. [.c. N $
>                         switchDOp :@ [ enumConstructors , enumBranches , NV c] ])

>   enumU :: Tm {In, p} x
>   enumU = MU (Just (ANCHOR (TAG "EnumU") SET ALLOWEDEPSILON)) enumD

>   enumREF :: REF
>   enumREF = [("Primitive", 0), ("EnumU", 0)] := DEFN enumU :<: SET 

>   enumDREF :: REF
>   enumDREF = [("Primitive", 0), ("EnumD", 0)] := DEFN enumD :<: desc

>   enumConstructorsREF :: REF
>   enumConstructorsREF = [("Primitive", 0), ("EnumConstructors", 0)] :=
>       DEFN enumConstructors :<: enumU

>   enumBranchesREF :: REF
>   enumBranchesREF = [("Primitive", 0), ("EnumBranches", 0)] :=
>       DEFN enumBranches :<:
>           branchesOp @@ [enumConstructors, LK desc]

> import -> Primitives where
>   ("EnumU", enumREF)   :
>   ("EnumD", enumDREF)  :
>   ("EnumConstructors", enumConstructorsREF) :
>   ("EnumBranches", enumBranchesREF) :

> import -> CanConstructors where
>   EnumT  :: t -> Can t
>   Ze     :: Can t
>   Su     :: t -> Can t 

> import -> CanPats where
>   pattern ZE         = C Ze
>   pattern SU n       = C (Su n)

>   pattern NILN       = ZE
>   pattern CONSN      = SU ZE

>   pattern ENUMT e    = C (EnumT e) 
>   pattern NILE       = CON (PAIR NILN VOID)
>   pattern CONSE t e  = CON (PAIR CONSN (PAIR t (PAIR e VOID)))


> import -> CanDisplayPats where
>   pattern DENUMT e    = DC (EnumT e) 
>   pattern DNILE       = DCON (DPAIR {-(DTAG "nil")-} DZE DVOID)
>   pattern DCONSE t e  = DCON (DPAIR {- (DTAG "cons") -} (DSU DZE) (DPAIR t (DPAIR e DVOID)))
>   pattern DZE         = DC Ze
>   pattern DSU n       = DC (Su n)

> import -> CanCompile where
>   makeBody Ze = CTag 0
>   makeBody (Su x) = STag (makeBody x)

> import -> CanTraverse where
>   traverse f (EnumT e)    = (|EnumT (f e)|)
>   traverse f Ze           = (|Ze|)
>   traverse f (Su n)       = (|Su (f n)|) 

> import -> CanHalfZip where
>   halfZip (EnumT t0) (EnumT t1) = Just (EnumT (t0,t1))
>   halfZip Ze Ze = Just Ze
>   halfZip (Su t0) (Su t1) = Just (Su (t0,t1))

> import -> CanPretty where
>   pretty (EnumT t)  = wrapDoc (kword KwEnum <+> pretty t ArgSize) AppSize
>   pretty Ze         = const (int 0)
>   pretty (Su t)     = prettyEnumIndex 1 t

> import -> Pretty where
>   prettyEnumIndex :: Int -> DInTmRN -> Size -> Doc
>   prettyEnumIndex n DZE      = const (int n)
>   prettyEnumIndex n (DSU t)  = prettyEnumIndex (succ n) t
>   prettyEnumIndex n tm       = wrapDoc
>       (int n <+> kword KwPlus <+> pretty tm ArgSize)
>       AppSize

> import -> CanTyRules where
>   canTy chev (Set :>: EnumT e)  = do
>     eev@(e :=>: ev) <- chev (enumU :>: e)
>     return $ EnumT eev
>   canTy _ (EnumT (CON e) :>: Ze)       | CONSN <- e $$ Fst  = return Ze 
>   canTy chev (EnumT (CON e) :>: Su n)  | CONSN <- e $$ Fst  = do
>     nnv@(n :=>: nv) <- chev (ENUMT (e $$ Snd $$ Snd $$ Fst) :>: n)
>     return $ Su nnv

> import -> OpCode where

>   type EnumDispatchTable = (VAL, VAL -> VAL -> VAL) 
>
>   mkLazyEnumDef :: VAL -> EnumDispatchTable -> Either NEU VAL
>   mkLazyEnumDef arg (nilECase, consECase) = let args = arg $$ Snd in
>       case arg $$ Fst of
>           NILN   -> Right $ nilECase
>           CONSN  -> Right $ consECase (args $$ Fst) (args $$ Snd $$ Fst)
>           N t    -> Left t
>           _      -> error "mkLazyEnumDef: invalid constructor!"

>   branchesOp = Op 
>     { opName   = "branches"
>     , opArity  = 2 
>     , opTyTel  = bOpTy
>     , opRun    = {-bOpRun-} runOpTree $
>         oData  [ oTup $ OLam $ \_P -> ORet UNIT
>                , oTup $ \ () _E -> OLam $ \_P -> ORet $
>                  TIMES (_P $$ A ZE)
>                     (branchesOp @@ [_E, L $ "x" :. [.x. _P -$ [SU (NV x)]]])
>                ]
>     , opSimp   = \_ _ -> empty
>     } where
>         bOpTy = "e" :<: enumU :-: \e ->
>                 "p" :<: ARR (ENUMT e) SET :-: \p ->
>                 Target SET

>   switchOp = Op
>     { opName  = "switch"
>     , opArity = 4
>     , opTyTel = sOpTy
>     , opRun   = runOpTree $ {- sOpRun -- makeOpRun "switch" switchTest -}
>         OLam $ \_ ->
>         OCase (map projector [0..])
>     , opSimp  = \_ _ -> empty
>     } where
>         projector i = OLam $ \_ -> OLam $ \bs -> ORet (proj i bs)
>         proj 0 bs = bs $$ Fst
>         proj i bs = proj (i - 1) (bs $$ Snd)
>         sOpTy = 
>           "e" :<: enumU :-: \e ->
>           "x" :<: ENUMT e :-: \x ->
>           "p" :<: ARR (ENUMT e) SET :-: \p ->
>           "b" :<: branchesOp @@ [e , p] :-: \b -> 
>           Target (p $$ A x)

>   enumInductionOp = Op
>     {  opName = "enumInduction"
>     ,  opArity = 5
>     ,  opTyTel = eOpTy
>     ,  opRun = runOpTree $
>        oData  [  oTup $ OSet $ \ c -> OBarf
>               ,  oTup $ \ t e ->
>                  OSet $ \ c ->
>                  oLams $ \ p mz ms -> 
>                  case c of
>                    Ze      -> ORet (mz $$ A t $$ A e)
>                    (Su x)  -> ORet (ms $$ A t $$ A e $$ A x $$ A
>                                            (enumInductionOp @@ [e, x, p, mz, ms]))
>               ]
>     ,  opSimp = \ _ _ -> empty
>     } where
>       eOpTy =
>         "e" :<: enumU :-: \ e ->
>         "x" :<: ENUMT e :-: \ x ->
>         "p" :<: ARR (SIGMA enumU (L $ "e" :. [.e. ENUMT (NV e)])) SET :-: \ p ->
>         "mz" :<: (PI UID $ L $ "t" :. [.t.
>                      PI enumU $ L $ "e" :. [.e.
>                          p -$ [PAIR (CONSE (NV t) (NV e)) ZE]
>                      ]]) :-: \ mz ->
>         "ms" :<: (PI UID $ L $ "t" :. [.t.
>                      PI enumU $ L $ "e" :. [.e.
>                      PI (ENUMT (NV e)) $ L $ "x" :. [.x.
>                      ARR (p -$ [PAIR (NV e) (NV x)])
>                          (p -$ [PAIR (CONSE (NV t) (NV e)) (SU (NV x))])
>                      ]]]) :-: \ ms ->
>         Target (p $$ A (PAIR e x))


> import -> Coerce where
>   coerce (EnumT (CONSE _ _,   CONSE _ _))      _  ZE = Right ZE
>   coerce (EnumT (CONSE _ e1,  CONSE _ e2))     q  (SU x) = Right . SU $
>     coe @@ [ENUMT e1, ENUMT e2, CON $ q $$ Snd $$ Snd $$ Fst, x]  -- |CONSE| tails
>   coerce (EnumT (NILE,        NILE))           q  x = Right x
>   coerce (EnumT (NILE,        t@(CONSE _ _)))  q  x = Right $
>     nEOp @@ [q, ENUMT t]
>   coerce (EnumT (CONSE _ _,   NILE))           q  x = Right $
>     nEOp @@ [q, ENUMT NILE]

> import -> Operators where
>   branchesOp :
>   switchOp :
>   enumInductionOp :

> import -> OpCompile where
>     ("branches", _) -> Ignore
>     ("switch", [e, x, p, b]) -> App (Var "__switch") [Ignore, x, Ignore, b]

> import -> OpGenerate where
>     ("switch", switchTest) :

> import -> KeywordConstructors where
>   KwEnum  :: Keyword
>   KwPlus  :: Keyword

> import -> KeywordTable where
>   key KwEnum      = "Enum"
>   key KwPlus      = "+"

> import -> DInTmParsersSpecial where
>   (ArgSize, (|mkNum (|read digits|) (optional $ (keyword KwPlus) *> sizedDInTm ArgSize)|)) :
>   (AndSize, (|DENUMT (%keyword KwEnum%) (sizedDInTm ArgSize)|)) :

> import -> ParserCode where
>     mkNum :: Int -> Maybe DInTmRN -> DInTmRN
>     mkNum 0 Nothing = DZE
>     mkNum 0 (Just t) = t
>     mkNum n t = DSU (mkNum (n-1) t)

A function from an enumeration is equivalent to a list, so the elaborator can
turn lists into functions like this:

> import -> MakeElabRules where
>   makeElab' loc (PI (ENUMT e) t :>: m) | isTuply m = do
>       t' :=>: _ <- eQuote t
>       e' :=>: _ <- eQuote e
>       tm :=>: tmv <- subElab loc (branchesOp @@ [e, t] :>: m)
>       x <- eLambda (fortran t)
>       return $ N (switchOp :@ [e', NP x, t', tm])
>                      :=>: switchOp @@ [e, NP x, t, tmv]
>     where
>       isTuply :: DInTmRN -> Bool
>       isTuply DVOID        = True
>       isTuply (DPAIR _ _)  = True
>       isTuply _            = False


To elaborate a tag with an enumeration as its type, we search for the
tag in the enumeration to determine the appropriate index.

>   makeElab' loc (ENUMT t :>: DTAG a) = findTag a t 0
>     where
>       findTag :: String -> TY -> Int -> Elab (INTM :=>: VAL)
>       findTag a (CONSE (TAG b) t) n
>         | a == b        = return (toNum n :=>: toNum n)
>         | otherwise     = findTag a t (succ n)
>       findTag a _ n  = throwError' . err $ "elaborate: tag `" 
>                                             ++ a 
>                                             ++ " not found in enumeration."
>                         
>       toNum :: Int -> Tm {In, p} x
>       toNum 0  = ZE
>       toNum n  = SU (toNum (n-1))

Conversely, we can distill an index to a tag as follows. Note that if the
index contains a stuck term, we simply give up and let the normal distillation
rules take over; the pretty-printer will then do the right thing.

> import -> DistillRules where
>   distill _ (ENUMT t :>: tm) | Just r <- findIndex (t :>: tm) = return r
>     where
>       findIndex :: (VAL :>: INTM) -> Maybe (DInTmRN :=>: VAL)
>       findIndex (CONSE (TAG s)  _ :>: ZE)    = Just (DTAG s :=>: evTm tm)
>       findIndex (CONSE _        a :>: SU b)  = findIndex (a :>: b)
>       findIndex _                            = Nothing

Since elaboration turns lists into functions from enumerated types, we can
do the reverse when distilling. This is slightly dubious.

>   distill es (PI (ENUMT e) t :>: L (x :. N (op :@ [e', NV 0, t', b]))) 
>     | op == switchOp = distill es (branchesOp @@ [e, t] :>: b)