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

> import -> SugarTactics where
>   impTac p q = can $ All (can $ Prf p)
>                          (lambda $ \_ -> q)

> import -> Check where
>   check (C (All s t) :>: L sc) r = 
>     Root.freshRef ("" :<: s) 
>              (\ref -> check (PRF (t $$ A (pval ref)) :>: underScope sc ref)) 
>              r

> import -> CanTyRules where
>   canTy _   (Set :>: Prop)           = return Prop
>   canTy chev  (Set :>: Prf p)         = do
>     ppv@(p :=>: pv) <- chev (PROP :>: p)
>     return $ Prf ppv
>   canTy chev  (Prop :>: All s p)       = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ppv@(p :=>: pv) <- chev (ARR sv PROP :>: p)
>     return $ All ssv ppv
>   canTy chev  (Prop :>: And p q)       = do
>     ppv@(p :=>: pv) <- chev (PROP :>: p)
>     qqv@(q :=>: qv) <- chev (PROP :>: q)
>     return $ And ppv qqv
>   canTy _  (Prop :>: Trivial)       = return Trivial
>   canTy _  (Prop :>: Absurd)        = return Absurd
>   canTy chev  (Prf p :>: Box (Irr x))  = do 
>     xxv@(x :=>: xv) <- chev (p :>: x)
>     return $ Box (Irr xxv)
>   canTy chev  (And p q :>: Pair x y)   = do
>     xxv@(x :=>: xv) <- chev (PRF p :>: x)
>     yyv@(y :=>: yv) <- chev (PRF q :>: y)
>     return $ Pair xxv yyv
>   canTy _   (Trivial :>: Void)       = return Void

> import -> ElimConstructors where
>   UnBox    :: Elim t

> import -> TraverseElim where
>   traverse _ UnBox = (|UnBox|)

> import -> ElimTyRules where
>   elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>     eev@(e :=>: ev) <- chev (p :>: e)
>     return $ (A eev, PRF (q $$ A ev))
>   elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
>   elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)
>   elimTy chev (_ :<: Prf p)              UnBox  = return (UnBox, p)

> import -> ElimComputation where
>   C (Box (Irr p))    $$ UnBox  = p -- only for eta-expand?

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
>               opty _ _      = traceErr "naughtE: invalid arguments"
>               oprun :: [VAL] -> Either NEU VAL
>               oprun [N z,ty] = Left z

> import -> Operators where
>   nEOp :

> import -> EtaExpand where
>   etaExpand (C (All s t) :>: f) r = Just $
>     L ("etaAll" :. fresh ("" :<: s) 
>       (\v  -> inQuote (C (Prf (t $$ A v)) :>: (f $$ A v))) r)
>   etaExpand (PRF p :>: x) r = Just (BOX (Irr (inQuote (p :>: x $$ UnBox) r))))
>   etaExpand (AND p q :>: pq) r =  
>     (| (\x y -> PAIR x y) (etaExpand (PRF p :>: (pq $$ Fst)) r) 
>                           (etaExpand (PRF q :>: (pq $$ Snd)) r) |)

> import -> OpRunEqGreen
>   opRunEqGreen [PROP,t1,PROP,t2] = Right $ AND (IMP t1 t2) (IMP t2 t1)
>   opRunEqGreen [Prf _,_,Prf _,_] = Right TRIVIAL
