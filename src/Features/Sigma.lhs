\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Sigma where

%endif

\question{Do the Formation/Introduction/\ldots names make sense?}

\question{How do we handle the |Fst| and |Snd| eliminators?}


Formation rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Unit-formation}
\UnaryInfC{|Set :>: Unit|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|Set :>: S|}
\AxiomC{|Set -> Set :>: T|}
\RightLabel{Sigma-formation}
\BinaryInfC{|Set :>: Sigma S T|}
\end{prooftree}

Introduction rules:

\begin{prooftree}
\AxiomC{}
\RightLabel{Unit-intro}
\UnaryInfC{|Unit :>: Void|}
\end{prooftree}

\begin{prooftree}
\AxiomC{|S :>: x|}
\AxiomC{|T x :>: y|}
\RightLabel{Sigma-intro}
\BinaryInfC{|Sigma S T :>: Pair x y|}
\end{prooftree}

Elimination rules:

\begin{prooftree}
\AxiomC{|Set :>: A|}
\AxiomC{|A -> Set :>: B|}
\noLine
\BinaryInfC{|(a : A) (b : B a) -> C (Pair a b) :>: f|}
\AxiomC{|Sigma A B -> Set :>: C|}
\noLine
\UnaryInfC{|Sigma A B :>: t|}
\RightLabel{Sigma-elim}
\BinaryInfC{|C t :>: split(A,B,f,t)|}
\end{prooftree}

With the following computational behavior:

< split _ _ _ f t = f (fst t) (snd t)

Equality rules:

< eqGreen(Unit, _, Unit, _) :-> Trivial
< eqGreen(Sigma s1 t1, p1, Sigma s2 t2, p2) :->
<     And (eqGreen(s1, fst p1, s2, fst p2))
<         (eqGreen(t1 (fst p1), snd p1, t2 (fst p2), snd p2))

Coercion rule:


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
>   prettyPair :: InDTmRN -> Size -> Doc
>   prettyPair p = const (brackets (prettyPairMore empty p))

>   prettyPairMore :: Doc -> InDTmRN -> Doc
>   prettyPairMore d DVOID        = d
>   prettyPairMore d (DPAIR a b)  = prettyPairMore (d <+> pretty a minBound) b
>   prettyPairMore d t            = d <+> kword KwComma <+> pretty t maxBound

>   prettySigma :: Doc -> InDTmRN -> Size -> Doc
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


> import -> SugarTactics where
>     sigmaTac p q 
>         = can $ Sigma p (lambda q)
>     pairTac p q = can $ Pair p q
>     unitTac = can Unit
>     voidTac = can Void
>     timesTac p q
>         = can $ Sigma p (lambda $ \_ -> q)

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

> import -> HalfZipCan where
>   halfZip Unit Unit = Just Unit
>   halfZip (Sigma s0 t0) (Sigma s1 t1) = Just (Sigma (s0,s1) (t0,t1))
>   halfZip Void Void = Just Void
>   halfZip (Pair s0 t0) (Pair s1 t1) = Just (Pair (s0,s1) (t0,t1))

> import -> TraverseElim where
>   traverse f Fst  = (|Fst|)
>   traverse f Snd  = (|Snd|)

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
>     , opTyTel =  "A"   :<: SET :-: \ aA ->
>                  "B"   :<: ARR aA SET :-: \ bB ->
>                  "ab"  :<: SIGMA aA bB             :-: \ ab ->
>                  "P"   :<: ARR (SIGMA aA bB) SET   :-: \ pP ->
>                  "p"   :<: pity (
>                    "a" :<: aA :-: \ a -> 
>                    "b" :<: (bB $$ A a) :-: \ b -> 
>                    Target $ pP $$ A (PAIR a b))    :-: \ p ->
>                  Target $ pP $$ A ab
>     , opRun = \ [_ , _ , ab , _ , p] -> Right $ p $$ A (ab $$ Fst) $$ A (ab $$ Snd)
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
