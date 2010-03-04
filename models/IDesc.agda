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

data Lifted {l : Level} (A : Set l) : Set (suc l) where
       lifter : A → Lifted A

lift : {i : Level} -> Set i -> Set (suc i) 
lift x =  Lifted x

unlift : {l : Level}{A : Set l} -> Lifted A -> A
unlift (lifter a) = a

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

--****************
-- Equality
--****************

data _==_ {l : Level}{A : Set l}(x : A) : A -> Set l where
  refl : x == x

cong : {l : Level}{A B : Set l}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong2 : {l : Level}{A B C : Set l}(f : A -> B -> C){x y : A}{z t : B} -> 
        x == y -> z == t -> f x z == f y t
cong2 f refl refl = refl


-- Intensionally extensional
postulate 
  reflFun : {l : Level}{A B : Set l}(f : A -> B)(g : A -> B)-> ((a : A) -> f a == g a) -> f == g 


--********************************************
-- Desc code
--********************************************

data IDesc {l : Level}(I : Set l) : Set (suc l) where
  var : I -> IDesc I
  const : Set l -> IDesc I
  prod : IDesc I -> IDesc I -> IDesc I
  sigma : (S : Set l) -> (S -> IDesc I) -> IDesc I
  pi : (S : Set l) -> (S -> IDesc I) -> IDesc I


--********************************************
-- Desc interpretation
--********************************************

desc : {l : Level}{I : Set l} -> IDesc I -> (I -> Set l) -> Set l
desc (var i) P = P i
desc (const X) P = X
desc (prod D D') P = desc D P * desc D' P
desc (sigma S T) P = Sigma S (\s -> desc (T s) P)
desc (pi S T) P = (s : S) -> desc (T s) P

--********************************************
-- Fixpoint construction
--********************************************

data IMu {l : Level}{I : Set l}(R : I -> IDesc I)(i : I) : Set l where
  con : desc (R i) (\j -> IMu R j) -> IMu R i

--********************************************
-- Predicate: Box
--********************************************

box : {l : Level}{I : Set l}(D : IDesc I)(P : I -> Set l) -> desc D P -> IDesc (Sigma I P)
box (var i)     P x        = var (i , x)
box (const X)   P x        = const X
box (prod D D') P (d , d') = prod (box D P d) (box D' P d')
box (sigma S T) P (a , b)  = box (T a) P b
box (pi S T)    P f        = pi S (\s -> box (T s) P (f s))

--********************************************
-- Elimination principle: induction
--********************************************

module Elim {l : Level}
            {I : Set l}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set l)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (box (R i) (IMu R) xs) P) ->
                 P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> 
           (xs : desc D (IMu R)) -> 
           desc (box D (IMu R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : {l : Level}
            {I : Set l}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set l)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (box (R i) (IMu R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu R i) -> P ( i , x )
induction = Elim.induction

--********************************************
-- DescD
--********************************************

data DescDConst {l : Level} : Set l where
  lvar   : DescDConst
  lconst : DescDConst
  lprod  : DescDConst
  lpi    : DescDConst
  lsigma : DescDConst

descDChoice : {l : Level} -> Set l -> DescDConst -> IDesc Unit
descDChoice I lvar = const (lift I)
descDChoice _ lconst = const (Set _)
descDChoice _ lprod = prod (var Void) (var Void)
descDChoice _ lpi = sigma (Set _) (\S -> pi (lift S) (\s -> var Void))
descDChoice _ lsigma = sigma (Set _) (\S -> pi (lift S) (\s -> var Void))

descD : {l : Level}(I : Set l) -> IDesc Unit
descD I = sigma DescDConst (descDChoice I)

IDescl : {l : Level}(I : Set l) -> Set (suc l)
IDescl I = IMu (\_ -> descD I) Void

varl : {l : Level}{I : Set l}(i : I) -> IDescl I
varl {x} i = con (lv , lifter i) 
     where lv : DescDConst {l = suc x}
           lv = lvar

constl : {l : Level}{I : Set l}(X : Set l) -> IDescl I
constl {x} X = con (lc , X)
       where lc : DescDConst {l = suc x}
             lc = lconst

prodl : {l : Level}{I : Set l}(D D' : IDescl I) -> IDescl I
prodl {x} D D' = con (lp , (D , D'))
      where lp : DescDConst {l = suc x}
            lp = lprod


pil : {l : Level}{I : Set l}(S : Set l)(T : S -> IDescl I) -> IDescl I
pil {x} S T = con (lp , ( S , Tl))
    where lp : DescDConst {l = suc x}
          lp = lpi
          Tl : Lifted S -> IDescl _
          Tl (lifter s) = T s

sigmal : {l : Level}{I : Set l}(S : Set l)(T : S -> IDescl I) -> IDescl I
sigmal {x} S T = con (ls , ( S , Tl))
       where ls : DescDConst {l = suc x}
             ls = lsigma
             Tl : Lifted S -> IDescl _
             Tl (lifter s) = T s
             

--********************************************
-- From the embedding to the host
--********************************************

cases : {l : Level}
        {I : Set l}
        (xs : desc (descD I) (IMu (λ _ -> descD I)))
        (hs : desc (box (descD I) (IMu (λ _ -> descD I)) xs) (λ _ -> IDesc I)) ->
        IDesc I
cases ( lvar , i ) hs =  var (unlift i)
cases ( lconst , X ) hs =  const X
cases ( lprod , (D , D') ) ( d , d' ) =  prod d d'
cases ( lpi , ( S , T ) ) hs =  pi S (\s -> hs (lifter s))
cases ( lsigma , ( S , T ) ) hs = sigma S (\s -> hs (lifter s))

phi : {I : Set} -> IDescl I -> IDesc I
phi {I} d = induction (\_ -> descD I) (\_ -> IDesc I) (\_ -> cases) Void d

--********************************************
-- From the host to the embedding
--********************************************

psi : {I : Set} -> IDesc I -> IDescl I
psi (var i) = varl i
psi (const X) = constl X
psi (prod D D') = prodl (psi D) (psi D')
psi (pi S T) = pil S (\s -> psi (T s))
psi (sigma S T) = sigmal S (\s -> psi (T s))

