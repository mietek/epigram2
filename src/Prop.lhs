> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Prop where

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
>   pattern ALL p q = C (All p q)
>   pattern AND p q = C (And p q)
>   pattern TRIVIAL = C Trivial
>   pattern ABSURD  = C Absurd
>   pattern BOX p   = C (Box p)

> import -> CanTyRules where
>   canTy _  (Set :>: Prop)          = Just Prop
>   canTy _  (Set :>: Prf p)         = Just (Prf (PROP :>: p))
>   canTy ev (Prop :>: All p q)      = Just (All (SET :>: p) 
>                                                (Arr (ev p) PROP :>: q))
>   canTy _  (Prop :>: And p q)      = Just (And (PROP :>: p) (PROP :>: q))
>   canTy _  (Prop :>: Trivial)      = Just Trivial
>   canTy _  (Prop :>: Absurd)       = Just Absurd
>   canTy _  (Prf p :>: Box (Irr x)) = Just (Box (Irr (PRF p :>: x)))
>   canTy _  (And p q :>: Pair x y)  = Just (Pair (PRF p :>: x) (PRF q :>: y))
>   canTy _  (Trivial :>: Void)      = Just Void

> import -> ElimTyRules where
>   elimTy ev (Prf (ALL p q) :>: f)        (A e) = 
>     Just (A (p :>: e),q $$ A (ev e))
>   elimTy ev (Prf (AND p q) :>: PAIR x y) Fst   = Just (Fst,x)
>   elimTy ev (Prf (AND p q) :>: PAIR x y) Snd   = Just (Snd,y)

> import -> OpCode where
>   nEOp = Op { opName = "naughtE"
>             , opArity = 2
>             , opTy = opty
>             , opRun = oprun
>             } where
>               opty f [z,ty] = Just ([ PRF ABSURD :>: z,SET :>: ty ],f ty)
>               opty _ _      = Nothing
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