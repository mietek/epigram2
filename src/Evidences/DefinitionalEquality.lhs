
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
>     compare {n} (etaQuoten {n} (t' :>: x)) (etaQuoten {n} (t' :>: y)))



> compare :: forall p s . pi (n :: Nat) . Tm {p, s, n} -> Tm {p, s, n} -> Bool
> compare {n} (LK b1)        (LK b2)        = compare {n} b1 b2
> compare {n} (L ENil _ b1)  (L ENil _ b2)  = compare {S n} b1 b2
> compare {n} (c1 :- es1)    (c2 :- es2)    = 
>   c1 == c2 && maybe False id (| (F.all (uncurry (compare {n}))) (halfZip es1 es2) |)
> compare {n} (h1 :$ es1)    (h2 :$ es2)    = 
>   compare {n} h1 h2 && 
>   maybe False id (| (F.all (uncurry (compareE {n}))) (halfZip es1 es2) |)
> compare {n} (D d1 es1 _)   (D d2 es2 _)   = 
>   d1 == d2 && maybe False id (| (F.all (uncurry (compare {Z}))) (halfZip es1 es2) |)
> compare {n} (V i)          (V j)          = i == j
> compare {n} (P (i, _, _))  (P (j, _, _))  = i == j
> compare {n} x              y              = False

> compareE :: forall p s . pi (n :: Nat) . Elim (Tm {p, s, n}) -> Elim (Tm {p, s, n}) -> Bool
> compareE {n} (A x) (A y)  = compare {n} x y
> compareE {_} Hd    Hd     = True
> compareE {_} Tl    Tl     = True
> compareE {_} Out   Out    = True
> compareE {_} _     _      = False
