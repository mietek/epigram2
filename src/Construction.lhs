\section{Construction}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

> module Construction where

> import Control.Applicative
> import Data.Foldable hiding (foldl)
> import Data.Traversable
> import Data.Either
> import Control.Monad
> import MissingLibrary
> import BwdFwd
> import Features
> import Tm
> import Root
> import Rules
> import CoreLoad -- probably not the right thing to do

> type Cxty x = (Bwd REF, ENV) -> Root -> x

> deb :: REF -> Cxty EXTM
> deb x (g, _) _ = V (vf g) where
>   vf (g :< s) | x == s     =  0
>               | otherwise  = 1 + vf g
>   vf _                      = error "discharging non var in Construction"

> cLam :: String -> (REF -> TY -> Cxty INTM) -> TY -> Cxty INTM
> cLam n f (C (Pi s t)) (g, e) = freshRef (n :<: s) $ \ x ->
>   f x (t $$ A (pval x)) (g :< x, e :< pval x)

> cC :: Can (TY -> Cxty INTM) -> TY -> Cxty INTM
> cC ca (C ty) g@(_, e) r = C tm where
>   Just tm = canTy (\ y k -> let t = k y g r in (t, eval t e)) (ty :>: ca)


%endif

