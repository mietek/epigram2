\section{Prop}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Prop where

%endif

> import -> CanConstructors where
>   Prop    :: Can t
>   Prf     :: t -> Can t
>   All     :: t -> t -> Can t
>   And     :: t -> t -> Can t
>   Trivial :: Can t
>   Absurd  :: Can t
>   Box     :: Irr t -> Can t

Elim forms inherited from elsewhere

> import -> TraverseCan where
>   traverse _ Prop      = (|Prop|)
>   traverse f (Prf p)   = (|Prf (f p)|)
>   traverse f (All p q) = (|All (f p) (f q)|)
>   traverse f (And p q) = (|And (f p) (f q)|)
>   traverse _ Trivial   = (|Trivial|)
>   traverse _ Absurd    = (|Absurd|)
>   traverse f (Box p)   = (|Box (traverse f p)|)

> import -> CanPats where
>   pattern PROP    = C Prop
>   pattern PRF p   = C (Prf p)
>   pattern IMP p q = C (All (PRF p) (L (K q)))
>   pattern ALL p q = C (All p q)
>   pattern AND p q = C (And p q)
>   pattern TRIVIAL = C Trivial
>   pattern ABSURD  = C Absurd
>   pattern BOX p   = C (Box p)

> import -> CanTyRules where
>   canTy _   (Set :>: Prop)           = return Prop
>   canTy ev  (Set :>: Prf p)          = do
>     pv <- ev p
>     return $ Prf (PROP :>: p)
>   canTy ev  (Prop :>: All s p)       = do
>     sv <- ev s
>     pv <- ev p
>     return $ All (SET :>: s) (ARR sv PROP :>: p)
>   canTy ev  (Prop :>: And p q)       = do
>     pv <- ev p
>     qv <- ev q
>     return $ And (PROP :>: p) (PROP :>: q)
>   canTy _  (Prop :>: Trivial)       = return Trivial
>   canTy _   (Prop :>: Absurd)        = return Absurd
>   canTy ev  (Prf p :>: Box (Irr x))  = do
>     xv <- ev x 
>     return $ Box (Irr (PRF p :>: x))
>   canTy ev  (And p q :>: Pair x y)   = do
>     xv <- ev x
>     yv <- ev y
>     return $ Pair (PRF p :>: x) (PRF q :>: y)
>   canTy _   (Trivial :>: Void)       = return Void


> import -> ElimTyRules where
>   elimTy ev (f :<: Prf (ALL p q))      (A e)  = 
>     Just (A (p :>: e),q $$ A (ev e))
>   elimTy ev (_ :<: Prf (AND p q))      Fst    = Just (Fst, PRF p)
>   elimTy ev (_ :<: Prf (AND p q))      Snd    = Just (Snd, PRF q)

> import -> OpCode where
>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTy = opty
>             , opRun = oprun
>             } where
>               opty chev [z,ty] = do
>                    (z :=>: zv) <- chev (PRF ABSURD :>: z)
>                    (ty :=>: tyv) <- chev (SET :>: ty)
>                    return ([ z :=>: zv
>                            , ty :=>: tyv ]
>                           , tyv)
>               opty _ _      = mzero
>               oprun :: [VAL] -> Either NEU VAL
>               oprun [N z,ty] = Left z

> import -> Operators where
>   nEOp :

> import -> EtaExpand where
>   etaExpand (PRF p :>: x) r = Just (BOX (Irr (inQuote (PRF p :>: x) r))))

> import -> Check where
>   check (PRF (ALL p q) :>: L sc) r = do
>     freshRef ("" :<: p)
>              (\ref -> check (PRF (q $$ A (pval ref)) :>: underScope sc ref))
>              r

> import -> OpRunEqGreen
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [Prf _,_,Prf _,_] = Right TRIVIAL
