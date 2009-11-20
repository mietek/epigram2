\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Sigma where

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

\question{At first glance, the coerce rule does not respect the
          definition of the OTT paper.}

< coe(Sigma x1 y1, Sigma x2 y2, q, f) :-> 
<     \s1 -> coe(y2 s2, y1 s1, q s2 s1 q2, f s2)
<         where s2 = coe(x2, x1, fst q, s1)
<               q2 = coh(x2, x1, fst q, s1)


> import -> CanConstructors where
>   Unit   :: Can t
>   Void   :: Can t
>   Sigma  :: t -> t -> Can t
>   Pair   :: t -> t -> Can t 

> import -> CanPretty where
>   prettyCan ss Unit = parens empty
>   prettyCan ss Void = text "Void"
>   prettyCan ss (Sigma s t) = parens (text "Sigma" <+> pretty ss s <+> pretty ss t)
>   prettyCan ss (Pair a b) = parens (pretty ss a <> comma <+> pretty ss b)

> import -> ElimConstructors where
>   Fst    :: Elim t
>   Snd    :: Elim t

> import -> ElimPretty where
>   prettyElim ss Fst = text "Fst"
>   prettyElim ss Snd = text "Snd"

> import -> CanPats where
>   pattern SIGMA p q = C (Sigma p q)
>   pattern PAIR  p q = C (Pair p q)
>   pattern UNIT      = C Unit
>   pattern VOID      = C Void
>   pattern Times x y = Sigma x (L (K y))
>   pattern TIMES x y = C (Times x y)  

> import -> SugarTactics where
>     timesTac :: Tac VAL -> Tac VAL -> Tac VAL
>     timesTac p q
>         = can (Sigma p (lambda $ \_ -> q))

> import -> CanCompile where
>   makeBody (Pair x y) = Tuple [makeBody x, makeBody y]

> import -> ElimComputation where
>   PAIR x y $$ Fst = x
>   PAIR x y $$ Snd = y

> import -> ElimCompile where
>   makeBody (arg, Fst) = Proj (makeBody arg) 0
>   makeBody (arg, Snd) = Proj (makeBody arg) 1

> import -> TraverseCan where
>   traverse f Unit         = (|Unit|)
>   traverse f Void         = (|Void|)
>   traverse f (Sigma s t)  = (|Sigma (f s) (f t)|)
>   traverse f (Pair x y)   = (|Pair (f x) (f y)|) 

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

> import -> EtaExpand where
>   etaExpand (VOID :>: v) r = Just (UNIT)
>   etaExpand (ty@(SIGMA s t) :>: p) r = let x = p $$ Fst in 
>     (| (\x y -> PAIR x y) (etaExpand (s :>: x) r) 
>                   (etaExpand (t $$ (A x) :>: (p $$ Snd)) r) |)

> import -> OpCode where
>   splitOp = Op
>     { opName = "split" , opArity = 5
>     , opTy = sOpTy , opRun = sOpRun 
>     } where
>       sOpTy chev [a , b , c , f , t] = do
>                    (a :=>: av) <- chev (SET :>: a)
>                    (b :=>: bv) <- chev (ARR av SET :>: b)
>                    (c :=>: cv) <- chev (ARR (SIGMA av bv) SET :>: c)
>                    (f :=>: fv) <- chev (C (Pi av (L (H (B0 :< bv :< cv) "a" 
>                                             (PI "b" (N (V 2 :$ A (NV 0))) 
>                                              (N (V 2 :$ A (PAIR (NV 1) 
>                                                            (NV 0)))))))) :>: f)
>                    (t :=>: tv) <- chev (SIGMA av bv :>: t)
>                    return ([ a :=>: av
>                            , b :=>: bv
>                            , c :=>: cv
>                            , f :=>: fv
>                            , t :=>: tv ]
>                           , cv $$ A tv)
>       sOpRun :: [VAL] -> Either NEU VAL
>       sOpRun [_ , _ , _ , f , t] = Right $ f $$ A (t $$ Fst) $$ A (t $$ Snd)

> import -> Operators where
>   splitOp :

> import -> OpRunEqGreen where
>   opRunEqGreen [UNIT,_,UNIT,_] = Right TRIVIAL
>   opRunEqGreen [SIGMA s1 t1,p1,SIGMA s2 t2,p2] = Right $
>     AND (eqGreen @@ [s1,p1 $$ Fst,s2,p2 $$ Fst])
>         (eqGreen @@ [t1 $$ A (p1 $$ Fst),p1 $$ Snd,t2 $$ A (p2 $$ Fst),p2 $$ Snd])

> import -> Coerce where
>   coerce (Sigma (x1,x2) (y1,y2)) q p = 
>     PAIR (coe @@ [x1,x2,q $$ Fst,p $$ Fst]) 
>          (coe @@ [y1,y2,q $$ Snd,p $$ Snd]) 
>   coerce Unit        q s = s
