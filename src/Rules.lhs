> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances, PatternGuards #-}

> module Rules where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable
> import BwdFwd
> import Tm
> import Root
> import Features

> canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (VAL :>: VAL))
> canTy ev (Set :>: Set)    = Just Set
> canTy ev (Set :>: Pi s t) = 
>   Just (Pi (SET :>: ev s) (Arr (ev s) SET :>: ev t))
> import <- CanTyRules
> canTy _  _            = Nothing

> elimTy :: (t -> VAL) -> (Can VAL :>: VAL) -> Elim t ->
>           Maybe (Elim (VAL :>: t),VAL)
> elimTy ev (Pi s t :>: f) (A e) = Just (A (s :>: e),(t $$ A (ev e))) 
> import <- ElimTyRules
> elimTy _ _ _ = Nothing

> quop :: REF -> Root -> EXTM
> quop ref@(ns := _) r = help (bwdList ns) r
>   where 
>   help (ns :< (_,i)) (r,j) = if ns == r then V (j-i-1) else P ref

> bquote :: Tm {d,VV} REF -> Root -> Tm {d,TT} REF
> bquote (L (H vs x t)) r = 
>  L (x :. fresh (x :<: undefined) (\x -> bquote (eval t (vs :< x))) r)
> bquote (L (K t))      r = L (K (bquote t r))
> bquote (C c)          r = C (traverse bquote c r)
> bquote (N n)          r = N (bquote n r)
> bquote (P x)          r = quop x r
> bquote (n :$ v)       r = bquote n r :$ traverse bquote v r

> etaExpand :: (VAL :>: VAL) -> Root -> Maybe INTM
> etaExpand (C (Pi s t) :>: f) r = Just $
>   L ("" :. fresh ("" :<: s) (\v  -> inQuote (t $$ A v :>: (f $$ A v))) r)
> import <- EtaExpand
> etaExpand _                  _ = Nothing

> inQuote :: (VAL :>: VAL) -> Root -> INTM
> inQuote tyv              r | Just t    <- etaExpand tyv r = t
> inQuote (_ :>: N n)      r | (t :<: _) <- exQuote n r = N t
> inQuote (C cty :>: C cv) r | Just x    <- canTy id (cty :>: cv) =
>   C $ traverse inQuote x r

> unC :: VAL -> Can VAL
> unC (C c) = c

> exQuote :: NEU -> Root -> (EXTM :<: VAL)
> exQuote (P x@(_ := DECL ty)) r = quop x r :<: ty
> exQuote (n :$ v)             r = (n' :$ traverse inQuote e r) :<: ty'
>   where
>   (n' :<: ty) = exQuote n r
>   Just (e,ty') = elimTy id (unC ty :>: N n) v

> quote :: (VAL :>: VAL) -> Root -> INTM
> quote vty r = inQuote vty (room r "quote")

> equal :: (VAL :>: (VAL,VAL)) -> Root -> Bool
> equal (ty :>: (v1,v2)) r = quote (ty :>: v1) r == quote (ty :>: v2) r
