
\section{Definitional Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

> module Evidences.DefinitionalEquality where

> import Prelude hiding (foldl, exp, compare)
> import ShePrelude

> import Control.Applicative
> import Control.Monad.Error
> import qualified Data.Monoid as M
> import Data.Foldable as F
> import Data.List hiding (foldl)
> import Data.Traversable

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import Kit.NatFinVec

> import Evidences.Tm
> import Evidences.EtaQuote

%endif

> equal :: Int -> (TY :>: (EXP,EXP)) -> Bool
> equal l (t :>: (x, y)) = intNat l (\ n -> 
>     let t' = ev t in
>     compare (etaQuoten {n} (t' :>: x)) (etaQuoten {n} (t' :>: y)))

> compare :: Tm {p, s, n} -> Tm {p, s, n} -> Bool
> compare (LK b1)        (LK b2)        = compare b1 b2
> compare (L ENil _ b1)  (L ENil _ b2)  = compare b1 b2
> compare (c1 :- es1)    (c2 :- es2)    = 
>   c1 == c2 && maybe False id (| (F.all (uncurry compare)) (halfZip es1 es2) |)
> compare (h1 :$ es1)    (h2 :$ es2)    = 
>   compare h1 h2 && 
>   maybe False id (| (F.all (uncurry compareE)) (halfZip es1 es2) |)
> compare (D d1 es1 _)   (D d2 es2 _)   = 
>   d1 == d2 && maybe False id (| (F.all (uncurry compare)) (halfZip es1 es2) |)
> compare (V i)          (V j)          = i == j
> compare (P (i, _, _))  (P (j, _, _))  = i == j
> compare _              _              = False

> compareE :: Elim (Tm {p, s, n}) -> Elim (Tm {p, s, n}) -> Bool
> compareE (A x) (A y)  = compare x y
> compareE Hd    Hd     = True
> compareE Tl    Tl     = True
> compareE Out   Out    = True
> compareE _     _      = False
