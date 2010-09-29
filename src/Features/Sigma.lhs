\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Sigma where

%endif


> import -> CanConstructors where
>   Unit   :: Can t
>   Void   :: Can t
>   Sigma  :: t -> t -> Can t
>   Pair   :: t -> t -> Can t 

> import -> CanPretty where
>   pretty Unit         = wrapDoc (kword KwSig <+> parens empty) AppSize
>   pretty Void         = prettyPair DVOID
>   pretty (Sigma s t)  = prettySigma empty (DSIGMA s t)
>   pretty (Pair a b)   = prettyPair (DPAIR a b)

> import -> Pretty where
>   prettyPair :: DInTmRN -> Size -> Doc
>   prettyPair p = const (brackets (prettyPairMore empty p))

>   prettyPairMore :: Doc -> DInTmRN -> Doc
>   prettyPairMore d DVOID        = d
>   prettyPairMore d (DPAIR a b)  = prettyPairMore (d <+> pretty a minBound) b
>   prettyPairMore d t            = d <+> kword KwComma <+> pretty t maxBound

>   prettySigma :: Doc -> DInTmRN -> Size -> Doc
>   prettySigma d DUNIT                      = prettySigmaDone d empty
>   prettySigma d (DSIGMA s (DL (x ::. t)))  = prettySigma
>       (d <+> text x <+> kword KwAsc <+> pretty s maxBound <+> kword KwSemi) t
>   prettySigma d (DSIGMA s (DL (DK t)))     = prettySigma
>       (d <+> pretty s maxBound <+> kword KwSemi) t
>   prettySigma d (DSIGMA s t) = prettySigmaDone d 
>       (kword KwSig <+> pretty s minBound <+> pretty t minBound)
>   prettySigma d t = prettySigmaDone d (pretty t maxBound)

>   prettySigmaDone :: Doc -> Doc -> Size -> Doc
>   prettySigmaDone s t
>     | isEmpty s  = wrapDoc t AppSize
>     | otherwise  = wrapDoc (kword KwSig <+> parens (s <+> t)) AppSize

> import -> ElimConstructors where
>   Fst    :: Elim t
>   Snd    :: Elim t

> import -> ElimPretty where
>   pretty Fst = const (kword KwFst)
>   pretty Snd = const (kword KwSnd)

> import -> CanPats where
>   pattern SIGMA p q = C (Sigma p q)
>   pattern PAIR  p q = C (Pair p q)
>   pattern UNIT      = C Unit
>   pattern VOID      = C Void
>   pattern Times x y = Sigma x (L (K y))
>   pattern TIMES x y = C (Times x y)  

> import -> CanDisplayPats where
>   pattern DSIGMA p q = DC (Sigma p q)
>   pattern DPAIR  p q = DC (Pair p q)
>   pattern DUNIT      = DC Unit
>   pattern DVOID      = DC Void
>   pattern DTimes x y = Sigma x (DL (DK y))
>   pattern DTIMES x y = DC (DTimes x y)


> import -> CanCompile where
>   makeBody (Pair x y) = Tuple [makeBody x, makeBody y]
>   makeBody Void = Tuple []

> import -> ElimComputation where
>   PAIR x y $$ Fst = x
>   PAIR x y $$ Snd = y

> import -> ElimCompile where
>   makeBody (arg, Fst) = Proj (makeBody arg) 0
>   makeBody (arg, Snd) = Proj (makeBody arg) 1

> import -> CanTraverse where
>   traverse f Unit         = (|Unit|)
>   traverse f Void         = (|Void|)
>   traverse f (Sigma s t)  = (|Sigma (f s) (f t)|)
>   traverse f (Pair x y)   = (|Pair (f x) (f y)|) 

> import -> CanHalfZip where
>   halfZip Unit Unit = Just Unit
>   halfZip (Sigma s0 t0) (Sigma s1 t1) = Just (Sigma (s0,s1) (t0,t1))
>   halfZip Void Void = Just Void
>   halfZip (Pair s0 t0) (Pair s1 t1) = Just (Pair (s0,s1) (t0,t1))

> import -> ElimTraverse where
>   traverse f Fst  = (|Fst|)
>   traverse f Snd  = (|Snd|)

> import -> ElimHalfZip where
>   halfZip Fst Fst = (|Fst|)
>   halfZip Snd Snd = (|Snd|)

> import -> CanTyRules where
>   canTy _   (Set :>: Unit) = return Unit
>   canTy chev  (Set :>: Sigma s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>     return $ Sigma ssv ttv
>   canTy _   (Unit :>: Void) = return Void
>   canTy chev  (Sigma s t :>: Pair x y) =  do
>     xxv@(x :=>: xv) <- chev (s :>: x)
>     yyv@(y :=>: yv) <- chev ((t $$ A xv) :>: y)
>     return $ Pair xxv yyv

> import -> ElimTyRules where
>   elimTy chev (_ :<: Sigma s t) Fst = return (Fst, s)
>   elimTy chev (p :<: Sigma s t) Snd = return (Snd, t $$ A (p $$ Fst))

> import -> CanEtaExpand where
>   etaExpand (Unit :>: v) r = Just VOID
>   etaExpand (Sigma s t :>: p) r = let x = p $$ Fst in 
>     Just (PAIR (inQuote (s :>: x) r) (inQuote (t $$ (A x) :>: (p $$ Snd)) r))

> import -> OpCompile where
>   ("split", [_,_,y,_,f]) -> App (Var "__split") [f,y] 

> import -> OpCode where
>   splitOp = Op
>     { opName = "split" , opArity = 5
>     , opTyTel =  "A"   :<: SET                          :-: \ aA ->
>                  "B"   :<: ARR aA SET                   :-: \ bB ->
>                  "ab"  :<: SIGMA aA bB                  :-: \ ab ->
>                  "P"   :<: ARR (SIGMA aA bB) SET        :-: \ pP ->
>                  "p"   :<: (
>                    PI aA $ L $ "a" :. [.a. 
>                     PI (bB -$ [ NV a ]) $ L $ "b" :. [.b.
>                      pP -$ [ PAIR (NV a) (NV b) ] ] ])  :-: \ p ->
>                  Target $ pP $$ A ab
>     , opRun = runOpTree $
>         oLams $ \ () () ab () p -> ORet $ p $$ A (ab $$ Fst) $$ A (ab $$ Snd)
>     , opSimp = \_ _ -> empty
>     }

> import -> Operators where
>   splitOp :

> import -> OpRunEqGreen where
>   opRunEqGreen [UNIT,_,UNIT,_] = Right TRIVIAL
>   opRunEqGreen [SIGMA s1 t1,p1,SIGMA s2 t2,p2] = Right $
>     AND (eqGreen @@ [s1,p1 $$ Fst,s2,p2 $$ Fst])
>         (eqGreen @@ [t1 $$ A (p1 $$ Fst),p1 $$ Snd,t2 $$ A (p2 $$ Fst),p2 $$ Snd])

> import -> Coerce where
>   coerce (Sigma (sS1, sS2) (tT1, tT2)) q p = Right . PAIR s2 $
>     coe @@ [  tT1 $$ A s1, tT2 $$ A s2
>            ,  CON $ q $$ Snd $$ A s1 $$ A s2 $$ A sq
>            ,  p $$ Snd] where
>       s1 = p $$ Fst
>       (s2, sq) = coeh sS1 sS2 (CON $ q $$ Fst) s1
>   coerce Unit q s = Right s


> import -> KeywordConstructors where
>   KwFst  :: Keyword
>   KwSnd  :: Keyword
>   KwSig  :: Keyword

> import -> KeywordTable where
>   key KwFst       = "!"
>   key KwSnd       = "-"
>   key KwSig       = "Sig"

> import -> ElimParsers where
>   (AppSize, (| Fst (%keyword KwFst%) |)) :
>   (AppSize, (| Snd (%keyword KwSnd%) |)) :

> import -> DInTmParsersSpecial where
>   (ArgSize, (|id (bracket Square tuple)|)) :
>   (ArgSize, (|id (%keyword KwSig%) (bracket Round sigma)|)) :
>   (ArgSize, (|DSIGMA (%keyword KwSig%) (sizedDInTm ArgSize) (sizedDInTm ArgSize)|)) :

> import -> ParserCode where
>     tuple :: Parsley Token DInTmRN
>     tuple =
>         (|DPAIR (sizedDInTm ArgSize) (| id (%keyword KwComma%) pDInTm
>                                       | id tuple |)
>          |DVOID (% pEndOfStream %)
>          |)

>     sigma :: Parsley Token DInTmRN
>     sigma = (|mkSigma (optional (ident <* keyword KwAsc)) pDInTm sigmaMore
>              |DUNIT (% pEndOfStream %)
>              |)

>     sigmaMore :: Parsley Token DInTmRN
>     sigmaMore = (|id (% keyword KwSemi %) (sigma <|> pDInTm)
>                  |(\p s -> mkSigma Nothing (DPRF p) s) (% keyword KwPrf %) pDInTm sigmaMore
>                  |(\x -> DPRF x) (% keyword KwPrf %) pDInTm
>                  |)

>     mkSigma :: Maybe String -> DInTmRN -> DInTmRN -> DInTmRN
>     mkSigma Nothing s t = DSIGMA s (DL (DK t))
>     mkSigma (Just x) s t = DSIGMA s (DL (x ::. t))



In order to make programs as cryptic as possible, you can use |con| in the
display language to generate a constant function from unit or curry a function
from a pair.

> import -> MakeElabRules where
>   makeElab' loc (PI UNIT t :>: DCON f) = do
>     tm :=>: tmv <- subElab loc (t $$ A VOID :>: f)
>     return $ LK tm :=>: LK tmv

>   makeElab' loc (PI (SIGMA d r) t :>: DCON f) = do
>     let mt =  PI d . L $ (fortran r) :. [.a. 
>               PI (r -$ [NV a]) . L $ (fortran t) :. [.b. 
>               t -$ [PAIR (NV a) (NV b)] ] ]
>     mt'  :=>: _    <- eQuote mt
>     tm   :=>: tmv  <- subElab loc (mt :>: f)
>     x <- eLambda (fortran t)
>     return $ N ((tm :? mt') :$ A (N (P x :$ Fst)) :$ A (N (P x :$ Snd)))
>                     :=>: tmv $$ A (NP x $$ Fst) $$ A (NP x $$ Snd)


> import -> DistillRules where
>   distill es (UNIT :>: _) = return $ DVOID :=>: VOID