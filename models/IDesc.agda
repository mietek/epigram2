{-# OPTIONS --universe-polymorphism #-}

module IDesc where

--********************************************
-- Prelude
--********************************************

-- Some preliminary stuffs, to avoid relying on the stdlib

--****************
-- Universe polymorphism
--****************

data Level : Set where
      zero : Level
      suc  : Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level -> Level -> Level
max  zero    m      = m
max (suc n)  zero   = suc n
max (suc n) (suc m) = suc (max n m)

{-# BUILTIN LEVELMAX max #-}

--****************
-- Sigma and friends
--****************

data Sigma {i j : Level}(A : Set i) (B : A -> Set j) : Set (max i j) where
  _,_ : (x : A) (y : B x) -> Sigma A B

_*_ : {i j : Level}(A : Set i)(B : Set j) -> Set (max i j)
A * B = Sigma A \_ -> B

fst : {i j : Level}{A : Set i}{B : A -> Set j} -> Sigma A B -> A
fst (a , _) = a

snd : {i j : Level}{A : Set i}{B : A -> Set j} (p : Sigma A B) -> B (fst p)
snd (a , b) = b

data Zero {i : Level} : Set i where
record One  {i : Level} : Set i where

--****************
-- Sum and friends
--****************

data _+_ {i j : Level}(A : Set i)(B : Set j) : Set (max i j) where
  l : A -> A + B
  r : B -> A + B



--********************************************
-- Desc code
--********************************************

data IDesc (I : Set) : Set1 where
  var : I -> IDesc I
  const : Set -> IDesc I
  prod : IDesc I -> IDesc I -> IDesc I
  sigma : (S : Set) -> (S -> IDesc I) -> IDesc I
  pi : (S : Set) -> (S -> IDesc I) -> IDesc I


--********************************************
-- Desc interpretation
--********************************************

desc : (I : Set) -> IDesc I -> (I -> Set) -> Set
desc I (var i) P = P i
desc I (const X) P = X
desc I (prod D D') P = desc I D P * desc I D' P
desc I (sigma S T) P = Sigma S (\s -> desc I (T s) P)
desc I (pi S T) P = (s : S) -> desc I (T s) P

--********************************************
-- Fixpoint construction
--********************************************

{-
data IMu (I : Set)(R : I -> IDesc I) : IDesc I -> Set1 where
  rec : (i : I) -> IMu I R (R i) -> IMu I R (var i)
  lambda : (S : Set i)(D : S -> IDesc I) -> ((s : S) -> IMu I R (D s)) -> IMu I R (pi S D)
  pair : (S : Set i)(D : S -> IDesc I) -> (Sigma S (\s -> IMu I R (D s))) -> IMu I R (sigma S D)