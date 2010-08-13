{-# OPTIONS --type-in-type #-}

-- Yeah, that's type-in-type. I'm a sissy, I want to use the stdlib, I
-- don't want to reimplement ℕ, ⊤, etc. in Set1.

module ILabel where

open import Data.String

open import Data.Empty
open import Data.Unit

open import Data.Product

open import Data.Maybe
open import Data.Nat

open import Relation.Binary.PropositionalEquality

--****************************************************************
-- A universe of labels
--****************************************************************

infixr 5 _∷_

data AllowedBy : Set -> Set where
  ε    : forall {T} -> 
         AllowedBy T
  _∷_  : {S : Set}{T : S -> Set} -> 
         (s : S)(ts : AllowedBy (T s)) -> AllowedBy ((x : S) -> T x)

UId = String

-- The universe (that's a tiny one):

data Label : Set where
  label : (u : UId)(T : Set)(ts : AllowedBy T) -> Label


--****************************************************************
-- IDesc & co.
--****************************************************************

data IDesc (I : Set1) : Set1 where
  var    : I -> IDesc I
  const  : Set -> IDesc I
  prod   : IDesc I -> IDesc I -> IDesc I
  sigma  : (S : Set) -> (S -> IDesc I) -> IDesc I
  pi     : (S : Set) -> (S -> IDesc I) -> IDesc I

desc : {I : Set1} -> IDesc I -> (I -> Set) -> Set
desc (var i) P = P i
desc (const X) P = X
desc (prod D D') P = desc D P × desc D' P
desc (sigma S T) P = Σ S (\s -> desc (T s) P)
desc (pi S T) P = (s : S) -> desc (T s) P

-- We (may) stuck a label on the fix-point:

data IMu {I : Set1}(L : Maybe (I -> Label))(R : I -> IDesc I)(i : I) : Set where
  con : desc (R i) (\j -> IMu L R j) -> IMu L R i



--****************************************************************
-- Example: Nat
--****************************************************************

data NatConst : Set where
  Ze : NatConst
  Su : NatConst

natCases : NatConst -> IDesc ⊤
natCases Ze = const ⊤
natCases Suc = var _

NatD : ⊤ → IDesc ⊤
NatD _ = sigma NatConst natCases

Nat : Set
Nat = IMu (just (\ _ -> label "Nat" Set ε)) NatD _

--****************************************************************
-- Example: Vector
--****************************************************************

data VecConst : ℕ -> Set where
  Vnil : VecConst 0
  Vcons : {n : ℕ} -> VecConst (1 + n)

vecDChoice : Set -> (n : ℕ) -> VecConst n -> IDesc ℕ
vecDChoice X 0 Vnil = const ⊤
vecDChoice X (suc n) Vcons = prod (const X) (var n)

vecD : Set -> ℕ -> IDesc ℕ
vecD X n = sigma (VecConst n) (vecDChoice X n)

vec : Set -> ℕ -> Set
vec X n = IMu (just (\n -> label "Vec" (ℕ -> Set) (n ∷ ε))) (vecD X) n

--****************
-- Example: Fin
--****************

data FinConst : ℕ -> Set where
  Fz : {n : ℕ} -> FinConst (1 + n)
  Fs : {n : ℕ} -> FinConst (1 + n)

finDChoice : (n : ℕ) -> FinConst n -> IDesc ℕ
finDChoice 0 ()
finDChoice (suc n) Fz = const ⊤
finDChoice (suc n) Fs = var n

finD : ℕ -> IDesc ℕ
finD n = sigma (FinConst n) (finDChoice n) 

fin : ℕ -> Set
fin n = IMu (just (\ n -> label "Fin" (ℕ -> Set) (n ∷ ε))) finD n


--****************
-- Example: Identity type
--****************

-- data Id (A : Set) (a : A) : A -> Set := (refl : Id A a a)

data IdConst : Set where
  Refl : IdConst 

idD : (A : Set)(a : A)(b : A) -> IDesc A
idD A a b = sigma IdConst (\ _ -> const (a ≡ b))

id : (A : Set)(a : A)(b : A) -> Set
id A a b = IMu (just (\ b -> label "Id" ((A : Set)(a : A)(b : A) -> Set) (A ∷ a ∷ b ∷ ε))) (idD A a) b
