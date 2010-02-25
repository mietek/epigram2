 {-# OPTIONS --type-in-type #-}

module IDesc_type_type where

--********************************************
-- Prelude
--********************************************

-- Some preliminary stuffs, to avoid relying on the stdlib

--****************
-- Sigma and friends
--****************

data Sigma (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) -> Sigma A B

_*_ : (A : Set)(B : Set) -> Set
A * B = Sigma A \_ -> B

fst : {A : Set}{B : A -> Set} -> Sigma A B -> A
fst (a , _) = a

snd : {A : Set}{B : A -> Set} (p : Sigma A B) -> B (fst p)
snd (a , b) = b

data Zero : Set where
data Unit  : Set where
  Void : Unit

--****************
-- Sum and friends
--****************

data _+_ (A : Set)(B : Set) : Set where
  l : A -> A + B
  r : B -> A + B

--********************************************
-- Desc code
--********************************************

data IDesc (I : Set) : Set where
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

data IMu (I : Set)(R : I -> IDesc I)(i : I) : Set where
  con : desc I (R i) (\j -> IMu I R j) -> IMu I R i

--********************************************
-- Predicate: Box
--********************************************

box : (I : Set)(D : IDesc I)(P : I -> Set) -> desc I D P -> IDesc (Sigma I P)
box I (var i)     P x        = var (i , x)
box I (const X)   P x        = const X
box I (prod D D') P (d , d') = prod (box I D P d) (box I D' P d')
box I (sigma S T) P (a , b)  = box I (T a) P b
box I (pi S T)    P f        = pi S (\s -> box I (T s) P (f s))

--********************************************
-- Elimination principle: induction
--********************************************

module Elim (I : Set)
            (R : I -> IDesc I)
            (P : Sigma I (IMu I R) -> Set)
            (m : (i : I)
                 (xs : desc I (R i) (IMu I R))
                 (hs : desc (Sigma I (IMu I R)) (box I (R i) (IMu I R) xs) P) ->
                 P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu I R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> 
           (xs : desc I D (IMu I R)) -> 
           desc (Sigma I (IMu I R)) (box I D (IMu I R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : (I : Set)
            (R : I -> IDesc I)
            (P : Sigma I (IMu I R) -> Set)
            (m : (i : I)
                 (xs : desc I (R i) (IMu I R))
                 (hs : desc (Sigma I (IMu I R)) (box I (R i) (IMu I R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu I R i) -> P ( i , x )
induction = Elim.induction


--********************************************
-- DescD
--********************************************

data DescDConst : Set where
  lvar   : DescDConst
  lconst : DescDConst
  lprod  : DescDConst
  lpi    : DescDConst
  lsigma : DescDConst

descDChoice : Set -> DescDConst -> IDesc Unit
descDChoice I lvar = const I
descDChoice _ lconst = const Set
descDChoice _ lprod = prod (var Void) (var Void)
descDChoice _ lpi = sigma Set (\S -> pi S (\s -> var Void))
descDChoice _ lsigma = sigma Set (\S -> pi S (\s -> var Void))

descD : (I : Set) -> IDesc Unit
descD I = sigma DescDConst (descDChoice I)

IDescl : (I : Set) -> Set
IDescl I = IMu Unit (\_ -> descD I) Void

varl : (I : Set)(i : I) -> IDescl I
varl I i = con (lvar ,  i)

constl : (I : Set)(X : Set) -> IDescl I
constl I X = con (lconst , X)

prodl : (I : Set)(D D' : IDescl I) -> IDescl I
prodl I D D' = con (lprod , (D , D'))

pil : (I : Set)(S : Set)(T : S -> IDescl I) -> IDescl I
pil I S T = con (lpi , ( S , T))

sigmal : (I : Set)(S : Set)(T : S -> IDescl I) -> IDescl I
sigmal I S T = con (lsigma , ( S , T))