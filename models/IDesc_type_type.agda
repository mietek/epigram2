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

--****************
-- Equality
--****************

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong2 : {A B C : Set}(f : A -> B -> C){x y : A}{z t : B} -> 
        x == y -> z == t -> f x z == f y t
cong2 f refl refl = refl


-- Intensionally extensional
postulate 
  reflFun : {A B : Set}(f : A -> B)(g : A -> B)-> ((a : A) -> f a == g a) -> f == g 

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

desc : {I : Set} -> IDesc I -> (I -> Set) -> Set
desc (var i) P = P i
desc (const X) P = X
desc (prod D D') P = desc D P * desc D' P
desc (sigma S T) P = Sigma S (\s -> desc (T s) P)
desc (pi S T) P = (s : S) -> desc (T s) P

--********************************************
-- Fixpoint construction
--********************************************

data IMu {I : Set}(R : I -> IDesc I)(i : I) : Set where
  con : desc (R i) (\j -> IMu R j) -> IMu R i

--********************************************
-- Predicate: Box
--********************************************

box : (I : Set)(D : IDesc I)(P : I -> Set) -> desc D P -> IDesc (Sigma I P)
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
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (box I (R i) (IMu R) xs) P) ->
                 P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> 
           (xs : desc D (IMu R)) -> 
           desc (box I D (IMu R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : (I : Set)
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (box I (R i) (IMu R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu R i) -> P ( i , x )
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
IDescl I = IMu (\_ -> descD I) Void

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

cases : (I : Set) 
        (xs : desc (descD I) (IMu (λ _ -> descD I)))
        (hs : desc (box Unit (descD I) (IMu (λ _ -> descD I)) xs) (λ _ -> IDesc I)) ->
        IDesc I
cases I ( lvar , i ) hs =  var i
cases I ( lconst , X ) hs =  const X
cases I ( lprod , (D , D') ) ( d , d' ) =  prod d d'
cases I ( lpi , ( S , T ) ) hs =  pi S hs
cases I ( lsigma , ( S , T ) ) hs = sigma S hs

iso1 : (I : Set) -> IDescl I -> IDesc I
iso1 I d = induction Unit (\_ -> descD I) (\_ -> IDesc I) (\_ -> cases I) Void d

iso2 : (I : Set) -> IDesc I -> IDescl I
iso2 I (var i) = varl I i
iso2 I (const X) = constl I X
iso2 I (prod D D') = prodl I (iso2 I D) (iso2 I D')
iso2 I (pi S T) = pil I S (\s -> iso2 I (T s))
iso2 I (sigma S T) = sigmal I S (\s -> iso2 I (T s))



proof-iso1-iso2 : (I : Set) -> (D : IDesc I) -> iso1 I (iso2 I D) == D
proof-iso1-iso2 I (var i) = refl
proof-iso1-iso2 I (const x) = refl
proof-iso1-iso2 I (prod D D') with proof-iso1-iso2 I D | proof-iso1-iso2 I D'
...                             | p | q = cong2 prod p q
proof-iso1-iso2 I (pi S T) = cong (pi S)  
                                  (reflFun (λ s → iso1 I (iso2 I (T s)))
                                           T
                                           (\s -> proof-iso1-iso2 I (T s)))
proof-iso1-iso2 I (sigma S T) = cong (sigma S) 
                                     (reflFun (λ s → iso1 I (iso2 I (T s)))
                                              T
                                              (\s -> proof-iso1-iso2 I (T s)))


P : (I : Set) -> Sigma Unit (IMu (λ x → sigma DescDConst (descDChoice I))) → Set
P I ( Void , D ) = iso2 I (iso1 I D) == D


proof-iso2-iso1 : (I : Set) -> (D : IDescl I) -> iso2 I (iso1 I D) == D
proof-iso2-iso1 I D =  induction Unit 
                                 (λ _ → descD I)
                                 (P I)
                                 (proof-iso2-iso1-casesW I) 
                                 Void
                                 D
                where proof-iso2-iso1-cases : (I : Set)
                                              (xs : Sigma DescDConst 
                                                    (λ s → desc (descDChoice I s)
                                                    (IMu (λ x → sigma DescDConst (descDChoice I)))))
                                              (hs : desc 
                                                    (box Unit (sigma DescDConst (descDChoice I))
                                                    (IMu (λ x → sigma DescDConst (descDChoice I))) xs)
                                                    (P I))
                                              → P I (Void , con xs)
                      proof-iso2-iso1-cases I (lvar , i) hs = refl
                      proof-iso2-iso1-cases I (lconst , x) hs = refl
                      proof-iso2-iso1-cases I (lprod , ( D , D' )) ( p , q ) = cong2 (prodl I) p q 
                      proof-iso2-iso1-cases I (lpi , ( S , T )) hs = cong (pil I S) 
                                                                          (reflFun (λ s → iso2 I (iso1 I (T s)))
                                                                                   T
                                                                                   hs)
                      proof-iso2-iso1-cases I (lsigma , ( S , T )) hs = cong (sigmal I S) 
                                                                             (reflFun (λ s → iso2 I (iso1 I (T s)))
                                                                                      T
                                                                                      hs)
                      proof-iso2-iso1-casesW : (I : Set)
                                               (i : Unit)
                                               (xs : Sigma DescDConst
                                                     (λ s → desc (descDChoice I s)
                                                     (IMu (λ x → sigma DescDConst (descDChoice I)))))
                                               (hs : desc 
                                                     (box Unit (sigma DescDConst (descDChoice I))
                                                     (IMu (λ x → sigma DescDConst (descDChoice I))) xs)
                                                     (P I))
                                                →  P I (i , con xs)
                      proof-iso2-iso1-casesW I Void = proof-iso2-iso1-cases I
                      

