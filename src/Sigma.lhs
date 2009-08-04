\section{Sigma}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Sigma where

%endif

> import -> CanConstructors where
>   Unit   :: Can t
>   Void   :: Can t
>   Sigma  :: t -> t -> Can t
>   Pair   :: t -> t -> Can t 

> import -> ElimConstructors where
>   Fst    :: Elim t
>   Snd    :: Elim t

> import -> CanPats where
>   pattern SIGMA p q = C (Sigma p q)
>   pattern PAIR  p q = C (Pair p q)
>   pattern UNIT      = C Unit
>   pattern VOID      = C Void
>   pattern Times x y = Sigma x (L (K y))
>   pattern TIMES x y = C (Times x y)  

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
>   canTy ev (Set :>: Unit) = Just Unit
>   canTy ev (Set :>: Sigma s t) = 
>     Just (Sigma (SET :>: s) (Arr (ev s) SET :>: t))
>   canTy ev (Unit :>: Void) = Just Void
>   canTy ev (Sigma s t :>: Pair x y) = 
>     Just (Pair (s :>: x) (t $$ A (ev x) :>: y))

> import -> ElimTyRules where
>   elimTy ev (_ :<: Sigma s t) Fst = Just (Fst, s)
>   elimTy ev (p :<: Sigma s t) Snd = Just (Snd, t $$ A (p $$ Fst))

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
>       sOpTy ev [a , b , c , f , t] = Just $
>         ([ SET :>: a , Arr va SET :>: b , Arr (SIGMA va vb) SET :>: c
>          , C (Pi va (L (H (B0 :< vb :< vc) "a" 
>                (PI "b" (N (V 2 :$ A (NV 0))) 
>                  (N (V 2 :$ A (PAIR (NV 1) (NV 0)))))))) :>: f
>          , (SIGMA va vb) :>: t ], vc $$ A (ev t))
>           where va = ev a
>                 vb = ev b
>                 vc = ev c
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
