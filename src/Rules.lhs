> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures,
>     TypeSynonymInstances, FlexibleInstances #-}

> module Rules where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable
> import BwdFwd
> import Tm
> import Root

> canTy :: (t -> VAL) -> (Can t, Can VAL) -> Maybe (Can (t, VAL))
> canTy ev (Set,Set)    = Just Set
> canTy ev (Pi s t,Set) = Just (Pi (s,SET) (t,Arr (ev s) SET))
> canTy _  _            = Nothing

> elimTy :: (t -> VAL) -> (VAL,Can VAL) -> Elim t ->
>           Maybe (Elim (t,VAL),(VAL,VAL))
> elimTy ev (f,Pi s t) (A e) = Just (A (e,s),(f $$ A v,t $$ A v)) 
>   where v = ev e

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