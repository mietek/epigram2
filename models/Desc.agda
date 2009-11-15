{-# OPTIONS --type-in-type
            --no-termination-check
            --no-positivity-check #-}

module Desc where

import Data.Product
import Data.Unit
import Data.Empty

open import Data.Product
open import Data.Unit
open import Data.Empty

-- Bringing in an hand-made Prop universe

data PROP : Set where
  All : (S : Set) -> (S -> PROP) -> PROP
  And : PROP -> PROP -> PROP
  Trivial : PROP
  Absurd : PROP

Prf : PROP -> Set
Prf Absurd = ⊥
Prf Trivial = ⊤
Prf (All S P) = (x : S) -> Prf (P x)
Prf (And A B) = Σ (Prf A)  (\ _ -> Prf B)


-- Then, we build Desc in Set
-- it's all Set in Set here

-- Desc code:
data Desc : Set where
  Done : Desc
  Arg : (X : Set) -> (X -> Desc) -> Desc
  Ind : (X : Set) -> Desc -> Desc

descOp : Desc -> Set -> Set
descOp Done _ = ⊤
descOp (Arg A f) D = Σ A (\ a -> descOp (f a) D)
descOp (Ind H x) D =  Σ (H -> D) (\ _ -> descOp x D)

-- Followed by Mu:

data Mu (X : Desc) : Set where
  Con : descOp X (Mu X) -> Mu X

-- All of this is fully-furnished with:
--   * boxOp
--   * mapBoxOp
--   * elimOp

boxOp : (d : Desc) -> (D : Set) -> (bp : D -> PROP) -> (v : descOp d D) -> Set
boxOp Done _ _ _ =  ⊤
boxOp (Arg A f) d p v =  boxOp (f (proj₁ v)) d p (proj₂ v)
boxOp (Ind H x) d p v =  Prf ( All H (\y -> p (proj₁ v y)))
                      × boxOp x d p (proj₂ v)


mapBoxOp : (d : Desc) -> (D : Set) -> (bp : D -> PROP) ->
           (Prf (All D (\y -> bp y))) -> (v : descOp d D) ->
           (boxOp d D bp v)
mapBoxOp Done _ _ _ _ =  tt
mapBoxOp (Arg a f) d bp p v =  mapBoxOp (f (proj₁ v)) d bp p (proj₂ v)
mapBoxOp (Ind H x) d bp p v =  (\ y -> p (proj₁ v y)) ,  mapBoxOp x d bp p (proj₂ v)

-- On the Ind case, the Pig code is saying something along those lines:
-- mapBoxOp (Ind H x) d bp p v =  (\ y -> p (proj₁ v y)) ,  mapBoxOp x d bp p (p?! (proj₂ v))



elimOp : (d : Desc) -> (bp : Mu d -> PROP) ->
         (Prf (All (descOp d (Mu d)) (\ x -> (All (boxOp d (Mu d) bp x) (\ _ -> bp (Con x)))))) ->
         (v : Mu d) -> Prf (bp v)
elimOp d bp p (Con v) =  p v (mapBoxOp d (Mu d) bp (\x -> elimOp d bp p x) v) 