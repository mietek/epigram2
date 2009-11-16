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

boxOp : (d : Desc) -> (D : Set) -> (bp : D -> Set) -> (v : descOp d D) -> Set
boxOp Done _ _ _ =  ⊤
boxOp (Arg A f) d p v =  boxOp (f (proj₁ v)) d p (proj₂ v)
boxOp (Ind H x) d p v =  ((y : H) -> p (proj₁ v y))
                      × boxOp x d p (proj₂ v)


mapBoxOp : (d : Desc) -> (D : Set) -> (bp : D -> Set) ->
           ((y : D) -> bp y) -> (v : descOp d D) ->
           (boxOp d D bp v)
mapBoxOp Done _ _ _ _ =  tt
mapBoxOp (Arg a f) d bp p v =  mapBoxOp (f (proj₁ v)) d bp p (proj₂ v)
mapBoxOp (Ind H x) d bp p v = (\y -> p (proj₁ v y)) ,  mapBoxOp x d bp p (proj₂ v)


elimOp : (d : Desc) -> (bp : Mu d -> Set) ->
         ((x : descOp d (Mu d)) -> (boxOp d (Mu d) bp x) -> bp (Con x)) ->
         (v : Mu d) -> bp v
elimOp d bp p (Con v) =  p v (mapBoxOp d (Mu d) bp (\x -> elimOp d bp p x) v) 