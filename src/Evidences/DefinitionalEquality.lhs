
\section{Definitional Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

> module Evidences.DefinitionalEquality where

> import Prelude hiding (foldl, exp)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import qualified Data.Monoid as M
> import Data.Foldable
> import Data.List hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Evidences.Tm
> import Evidences.EtaQuote

%endif

> tm2 = la "a" $ \a -> ZERO

> equal :: (TY :>: (EXP,EXP)) -> Bool
> equal (t :>: (x, y)) = 
>   let  xe = etaQuote (t :>: x)
>        ye = etaQuote (t :>: y)
>   in   xe == ye

> instance Eq (Tm {p, s, n}) where
>   LK b1        == LK b2        = b1 == b2
>   L ENil _ b1  == L ENil _ b2  = b1 == b2
>   (c1 :- es1)  == (c2 :- es2)  = c1 == c2 && es1 == es2
>   (h1 :$ es1)  == (h2 :$ es2)  = h1 == h2 && es1 == es2
>   D d1 es1 _   == D d2 es2 _   = d1 == d2 && es1 == es2
>   V i          == V j          = i == j
>   P (i, _, _)  == P (j, _, _)  = i == j
