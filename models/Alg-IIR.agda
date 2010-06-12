{-# OPTIONS --universe-polymorphism #-}

module IIR where
 
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

_o_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f o g = λ x → f (g x)
infixl 50 _o_

record Sg {a b : Level}(S : Set a)(T : S -> Set b) : Set (max a b) where
  constructor _,_
  field
    fst : S
    snd : T fst

infixr 40 _,_

record Lifted {l : Level} (A : Set l) : Set (suc l) where
  constructor lif
  field
    fil : A

open Lifted

lift : {i : Level} -> Set i -> Set (suc i) 
lift x =  Lifted x

unl : {l r : Level}{A : Set l}{P : Lifted A -> Set r} ->
      ((a : A) -> P (lif a)) -> (a : Lifted A) -> P a
unl p a = p (fil a)

mutual
  data IRD (I : Set1)(J : I -> Set1) : Set1 where
    var : I -> IRD I J
    con : Set -> IRD I J
    _*_ : (S : IRD I J) -> (Deco S -> IRD I J) -> IRD I J
    _>_ : (S : Set) -> (S -> IRD I J) -> IRD I J

  Deco : forall {I J} -> IRD I J -> Set1
  Deco {I}{J} (var i) = J i
  Deco (con A) = lift A -- grr
  Deco (S * T) = Sg (Deco S) \ s -> Deco (T s)
  Deco (S > T) = (s : S) -> Deco (T s)

_-:>_ : forall {a b c}{I : Set a} -> (I -> Set b) -> (I -> Set c)
        -> Set (max a (max b c))
_-:>_ {I = I} S T = (i : I) -> S i -> T i

mutual
  Func : forall {I J} -> IRD I J -> (X : I -> Set)(d : X -:> J) -> Set
  Func (var i) X d = X i
  Func (con A) X d = A
  Func (S * T) X d = Sg (Func S X d) \ s -> Func (T (deco S X d s)) X d
  Func (S > T) X d = (s : S) -> Func (T s) X d

  deco : forall {I J} -> (D : IRD I J) -> (X : I -> Set)(d : X -:> J) ->
           Func D X d -> Deco D
  deco (var i) X d x = d i x
  deco (con A) X d a = lif a
  deco (S * T) X d (s , t) = s' , t' where
    s' = deco S X d s
    t' = deco (T s') X d t
  deco (S > T) X d f = \ s -> deco (T s) X d (f s)

mutual
  data DATA {I J}(F : I -> IRD I J)(d : (Deco o F) -:> J)(i : I) : Set where
    <_> : Func (F i) (DATA F d) decode -> DATA F d i

  decode : forall {I J}{F : I -> IRD I J}{d : (Deco o F) -:> J} ->
           DATA F d -:> J
  decode {I}{J}{F}{d} i < xs > = d i (deco (F i) (DATA F d) decode xs)

data MyTags : Set where
  zz ss : MyTags

[_/_] : forall {l}{P : MyTags -> Set l} -> P zz -> P ss -> (t : MyTags) -> P t
[ z / s ] zz = z
[ z / s ] ss = s
        

record One {a} : Set a where
  constructor <>

NAT : One {suc zero} -> IRD One \ _ -> One
NAT _ = con MyTags * unl [ con One / var _ ]

Nat : Set
Nat = DATA NAT _ _

myze : Nat
myze = < zz , _ >

mysu : Nat -> Nat
mysu n = < ss , n >

data Two : Set where
  tt ff : Two

not : Two -> Two
not tt = ff
not ff = tt

_&&_ : Two -> Two -> Two
tt && b = b
ff && b = ff

_=N=_ : Nat -> Nat -> Two
< zz , _ > =N= < zz , _ > = tt
< zz , _ > =N= < ss , _ > = ff
< ss , _ > =N= < zz , _ > = ff
< ss , m > =N= < ss , n > = m =N= n

data Zero : Set where

So : Two -> Set
So tt = One
So ff = Zero

FREL :  One {suc zero} -> IRD One \ _ -> Lifted (Nat -> Two)
FREL _ = con MyTags * unl
           [ con One
           / (var _ * unl \ f -> con Nat * unl \ x -> con (So (f x)))
           ]

frel : Deco o FREL -:> \ _ -> Lifted (Nat -> Two)
frel _ (lif zz , _)                  = lif \ _ -> tt
frel _ (lif ss , lif f , lif x , p)  = lif \ y -> not (y =N= x) && f y

Frel : Set
Frel = DATA FREL frel _

good : Frel
good = < ss , < ss , < ss , < zz , _ > ,
         myze , _ > ,
         mysu myze , _ > ,
         mysu (mysu myze) , _ >

{-
bad : Frel
bad =  < ss , < ss , < ss , < zz , _ > ,
         myze , _ > ,
         mysu myze , _ > ,
         myze , {!!} >
-}

UNI :  One {suc zero} -> IRD One \ _ -> Set
UNI _ =  con MyTags * unl
           [ con One
           / (var _ * \ S -> S > \ _ -> var _)
           ]

uni : Deco o UNI -:> \ _ -> Set
uni i (lif zz , _) = Nat
uni i (lif ss , S , T) = (s : S) -> T s
