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

lift : {i : Level} -> Set i -> Set (suc i) 
lift = {!!}


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
data Unit  {i : Level} : Set i where
  Void : Unit

--****************
-- Sum and friends
--****************

data _+_ {i j : Level}(A : Set i)(B : Set j) : Set (max i j) where
  l : A -> A + B
  r : B -> A + B

--********************************************
-- Desc code
--********************************************

data IDesc (l : Level)(I : Set l) : Set (suc l) where
  var : I -> IDesc l I
  const : Set l -> IDesc l I
  prod : IDesc l I -> IDesc l I -> IDesc l I
  sigma : (S : Set l) -> (S -> IDesc l I) -> IDesc l I
  pi : (S : Set l) -> (S -> IDesc l I) -> IDesc l I


--********************************************
-- Desc interpretation
--********************************************

desc : (I : Set) -> IDesc zero I -> (I -> Set) -> Set
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
  lambda : (S : Set)(D : S -> IDesc I) -> ((s : S) -> IMu I R (D s)) -> IMu I R (pi S D)
  pair : (S : Set)(D : S -> IDesc I) -> (Sigma S (\s -> IMu I R (D s))) -> IMu I R (sigma S D)
-}

data IMu (I : Set)(R : I -> IDesc zero I)(i : I) : Set where
  con : desc I (R i) (\j -> IMu I R j) -> IMu I R i

--********************************************
-- Predicate: Box
--********************************************

box : (I : Set)(D : IDesc zero I)(P : I -> Set) -> desc I D P -> IDesc zero (Sigma I P)
box I (var i)     P x        = var (i , x)
box I (const X)   P x        = const X
box I (prod D D') P (d , d') = prod (box I D P d) (box I D' P d')
box I (sigma S T) P (a , b)  = box I (T a) P b
box I (pi S T)    P f        = pi S (\s -> box I (T s) P (f s))

--********************************************
-- Elimination principle: induction
--********************************************

module Elim (I : Set)
            (R : I -> IDesc zero I)
            (P : Sigma I (IMu I R) -> Set)
            (m : (i : I)(xs : desc I (R i) (IMu I R))(hs : desc (Sigma I (IMu I R)) (box I (R i) (IMu I R) xs) P) -> P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu I R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc zero I) -> (xs : desc I D (IMu I R)) -> desc (Sigma I (IMu I R)) (box I D (IMu I R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : (I : Set)(R : I -> IDesc zero I)(P : Sigma I (IMu I R) -> Set)
            (m : (i : I)
                 (xs : desc I (R i) (IMu I R))
                 (hs : desc (Sigma I (IMu I R)) (box I (R i) (IMu I R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu I R i) -> P ( i , x )
induction = Elim.induction


--********************************************
-- DescD
--********************************************

data DescDConst : Set1 where
  lvar   : DescDConst
  lconst : DescDConst
  lprod  : DescDConst
  lpi    : DescDConst
  lsigma : DescDConst

descDChoice : Set -> DescDConst -> IDesc (suc zero) Unit
descDChoice I lvar = const (lift I)
descDChoice _ lconst = const Set
descDChoice _ lprod = prod (var Void) (var Void)
descDChoice _ lpi = sigma Set (\S -> pi (lift S) (\s -> var Void))
descDChoice _ lsigma = sigma Set (\S -> pi (lift S) (\s -> var Void))

descD : (I : Set) -> IDesc (suc zero) Unit
descD I = sigma DescDConst (descDChoice I)

