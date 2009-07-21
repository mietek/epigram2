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

> import -> ElimComputation where
>   C (Pair x y) $$ Fst = x
>   C (Pair x y) $$ Snd = y

> import -> TraverseCan where
>   traverse f Unit         = (|Unit|)
>   traverse f Void         = (|Void|)
>   traverse f (Sigma s t)  = (|Sigma (f s) (f t)|)
>   traverse f (Pair x y)   = (|Pair (f x) (f y)|) 

> import -> TraverseElim where
>   traverse f Fst  = (|Fst|)
>   traverse f Snd  = (|Snd|)

> import -> CanPats where
>   pattern SIGMA p q = C (Sigma p q)
>   pattern PAIR  p q = C (Pair p q)
>   pattern UNIT      = C Unit
>   pattern VOID      = C Void

> import -> CanTyRules where
>   canTy ev (Set :>: Unit) = Just Unit
>   canTy ev (Set :>: Sigma s t) = 
>     Just (Sigma (SET :>: s) (Arr (ev s) SET :>: t))
>   canTy ev (Unit :>: Void) = Just Void
>   canTy ev (Sigma s t :>: Pair x y) = 
>     Just (Pair (s :>: x) (t $$ A (ev x) :>: y))

> import -> ElimTyRules where
>   elimTy ev (Sigma s t :>: p) Fst = Just (Fst,s)
>   elimTy ev (Sigma s t :>: p) Snd = Just (Snd,t $$ A (p $$ Fst))

> import -> EtaExpand where
>   etaExpand (VOID :>: v) r = Just (UNIT)
>   etaExpand (ty@(SIGMA s t) :>: p) r = let x = p $$ Fst in 
>     (| (\x y -> PAIR x y) (etaExpand (s :>: x) r) 
>                   (etaExpand (t $$ (A x) :>: (p $$ Snd)) r) |)  
