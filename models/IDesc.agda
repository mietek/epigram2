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

desc : (l : Level)(I : Set l) -> IDesc l I -> (I -> Set l) -> Set l
desc _ I (var i) P = P i
desc _ I (const X) P = X
desc x I (prod D D') P = desc x I D P * desc x I D' P
desc x I (sigma S T) P = Sigma S (\s -> desc x I (T s) P)
desc x I (pi S T) P = (s : S) -> desc x I (T s) P

--********************************************
-- Fixpoint construction
--********************************************

{-
data IMu (I : Set)(R : I -> IDesc I) : IDesc I -> Set1 where
  rec : (i : I) -> IMu I R (R i) -> IMu I R (var i)
  lambda : (S : Set)(D : S -> IDesc I) -> ((s : S) -> IMu I R (D s)) -> IMu I R (pi S D)
  pair : (S : Set)(D : S -> IDesc I) -> (Sigma S (\s -> IMu I R (D s))) -> IMu I R (sigma S D)
-}

data IMu (l : Level)(I : Set l)(R : I -> IDesc l I)(i : I) : Set l where
  con : desc l I (R i) (\j -> IMu l I R j) -> IMu l I R i

--********************************************
-- Predicate: Box
--********************************************

box : (l : Level)(I : Set l)(D : IDesc l I)(P : I -> Set l) -> desc l I D P -> IDesc l (Sigma I P)
box _ I (var i)     P x        = var (i , x)
box _ I (const X)   P x        = const X
box x I (prod D D') P (d , d') = prod (box x I D P d) (box x I D' P d')
box x I (sigma S T) P (a , b)  = box x I (T a) P b
box x I (pi S T)    P f        = pi S (\s -> box x I (T s) P (f s))

--********************************************
-- Elimination principle: induction
--********************************************

module Elim (l : Level)
            (I : Set l)
            (R : I -> IDesc l I)
            (P : Sigma I (IMu l I R) -> Set l)
            (m : (i : I)
                 (xs : desc l I (R i) (IMu l I R))
                 (hs : desc l (Sigma I (IMu l I R)) (box l I (R i) (IMu l I R) xs) P) ->
                 P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu l I R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc l I) -> 
           (xs : desc l I D (IMu l I R)) -> 
           desc l (Sigma I (IMu l I R)) (box l I D (IMu l I R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : (l : Level)
            (I : Set l)
            (R : I -> IDesc l I)
            (P : Sigma I (IMu l I R) -> Set l)
            (m : (i : I)
                 (xs : desc l I (R i) (IMu l I R))
                 (hs : desc l (Sigma I (IMu l I R)) (box l I (R i) (IMu l I R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu l I R i) -> P ( i , x )
induction = Elim.induction


--********************************************
-- DescD
--********************************************

data DescDConst (l : Level) : Set l where
  lvar   : DescDConst l
  lconst : DescDConst l
  lprod  : DescDConst l
  lpi    : DescDConst l
  lsigma : DescDConst l

descDChoice : (l : Level) -> Set l -> DescDConst (suc l) -> IDesc (suc l) Unit
descDChoice _ I lvar = const (lift I)
descDChoice x _ lconst = const (Set x)
descDChoice _ _ lprod = prod (var Void) (var Void)
descDChoice x _ lpi = sigma (Set x) (\S -> pi (lift S) (\s -> var Void))
descDChoice x _ lsigma = sigma (Set x) (\S -> pi (lift S) (\s -> var Void))

descD : (l : Level)(I : Set l) -> IDesc (suc l) Unit
descD x I = sigma (DescDConst (suc x)) (descDChoice x I)

IDescl : (l : Level)(I : Set l) -> Set (suc l)
IDescl x I = IMu (suc x) Unit (\_ -> descD x I) Void

{-
varl : (l : Level)(I : Set l) -> IDescl l I
varl x I = con (lvar , {!!})
-}

constl : (l : Level)(I : Set l)(X : Set l) -> IDescl l I
constl x I X = con (lconst , X)

prodl : (l : Level)(I : Set l)(D D' : IDescl l I) -> IDescl l I
prodl x I D D' = con (lprod , (D , D'))
