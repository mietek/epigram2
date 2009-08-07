{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check
 #-}

module Data1 where

_-_ : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set} ->
      ({a : A}(b : B a) -> C a b) -> (f : (a : A) -> B a) ->
      (a : A) -> C a (f a)
f - g = \ x -> f (g x)

id : {X : Set} -> X -> X
id x = x

konst : {S : Set}{T : S -> Set} -> ({x : S} -> T x) -> (x : S) -> T x
konst c x = c

data Zero : Set where
record One : Set where

record Sig (S : Set)(T : S -> Set) : Set where
  field
    fst : S
    snd : T fst

open module Sig' {S : Set}{T : S -> Set} = Sig {S}{T}

_,_ : forall {S T}(s : S) -> T s -> Sig S T
s , t = record {fst = s; snd = t}

infixr 40 _,_

_*_ : Set -> Set -> Set
S * T = Sig S \ _ -> T

sig : forall {S T}{P : Sig S T -> Set} ->
      ((s : S)(t : T s) -> P (s , t)) -> (st : Sig S T) -> P st
sig f st = f (fst st) (snd st)

data Cx : Set where
  E : Cx
  _/_ : Cx -> Set -> Cx

data _:>_ : Cx -> Set -> Set where
  ze : {G : Cx}{S : Set} -> (G / S) :> S
  su : {G : Cx}{S T : Set} -> G :> T -> (G / S) :> T

data PROP : Set where
  Absu : PROP
  Triv : PROP
  _/\_ : PROP -> PROP -> PROP
  All : (S : Set) -> (S -> PROP) -> PROP

Prf : PROP -> Set
Prf Absu = Zero
Prf Triv = One
Prf (P /\ Q) = Prf P * Prf Q
Prf (All S P) = (x : S) -> Prf (P x)

data CON (G : Cx) : Set where
  ?? : {S : Set} -> G :> S -> S -> CON G
  PrfC : PROP -> CON G
  _*C_ : CON G -> CON G -> CON G
  PiC : (S : Set) -> (S -> CON G) -> CON G
  SiC : (S : Set) -> (S -> CON G) -> CON G
  MuC : (O : Set) -> (O -> CON (G / O)) -> O -> CON G
  NuC : (O : Set) -> (O -> CON (G / O)) -> O -> CON G

Box : (G : Cx) -> ((S : Set) -> (G :> S) -> Set) -> Set
Box E F = One
Box (G / S) F = Box G (\ S n -> F S (su n)) * F S ze

pr : {G : Cx}{S : Set}{F : (S : Set) -> (G :> S) -> Set} -> Box G F -> (n : G :> S) -> F S n
pr fsf ze = snd fsf
pr fsf (su n) = pr (fst fsf) n

Pay : Cx -> Set
Pay G = Box G (\ I _ -> I -> Set)

Arr : (G : Cx) -> Pay G -> Pay G -> Set
Arr G X Y = Box G (\ S n -> (s : S) -> pr X n s -> pr Y n s)



mutual
  [|_|] : {G : Cx} -> CON G -> Pay G -> Set
  [| ?? n i |]     X = pr X n i
  [| PrfC P |]     X = Prf P
  [| C *C D |]     X = [| C |] X * [| D |] X
  [| PiC S C |]    X = (s : S) -> [| C s |] X
  [| SiC S C |]    X = Sig S \ s -> [| C s |] X
  [| MuC O C o |]  X = Mu C X o
  [| NuC O C o |]  X = Nu C X o

  data Mu {G : Cx}{O : Set}(C : O -> CON (G / O))(X : Pay G)(o : O) : Set where
    con : [| C o |] ( X , Mu C X ) -> Mu C X o
  codata Nu {G : Cx}{O : Set}(C : O -> CON (G / O))(X : Pay G)(o : O) : Set where
    con : [| C o |] ( X , Nu C X ) -> Nu C X o

noc :  {G : Cx}{O : Set}{C : O -> CON (G / O)}{X : Pay G}{o : O} ->
       Nu C X o -> [| C o |] ( X , Nu C X )
noc (con xs) = xs

mutual
  map : {G : Cx}{X Y : Pay G} -> (C : CON G) ->
        Arr G X Y ->
        [| C |] X -> [| C |] Y
  map (?? n i)     f = pr f n i
  map (PrfC P)     f = id
  map (C *C D)     f = sig \ c d -> map C f c , map D f d
  map (PiC S C)    f = \ c s -> map (C s) f (c s)
  map (SiC S C)    f = sig \ s c -> s , map (C s) f c
  map (MuC O C o)  f = foldMap C (Mu C _) f (\ o -> con) o
  map (NuC O C o)  f = unfoldMap C (Nu C _) f (\ o -> noc) o

  foldMap :  {G : Cx}{O : Set}(C : O -> CON (G / O)){X Y : Pay G}(Z : O -> Set) ->
          Arr G X Y ->
          ((o : O) -> [| C o |] ( Y , Z ) -> Z o) ->
          (o : O) -> Mu C X o -> Z o
  foldMap C Z f alg o (con xs) = alg o (map (C o) (f , foldMap C Z f alg) xs)

  unfoldMap :  {G : Cx}{O : Set}(C : O -> CON (G / O)){X Y : Pay G}(Z : O -> Set) ->
            Arr G X Y ->
            ((o : O) -> Z o -> [| C o |] ( X , Z )) ->
            (o : O) -> Z o -> Nu C Y o
  unfoldMap C Z f coalg o y = con (map (C o) (f , unfoldMap C Z f coalg) (coalg o y))

ida : (G : Cx) -> (X : Pay G) -> Arr G X X
ida E = id
ida (G / S) = sig \ Xs X -> ida G Xs , \ s x -> x

compa : (G : Cx) -> (X Y Z : Pay G) -> Arr G Y Z -> Arr G X Y -> Arr G X Z
compa E = \ _ _ _ _ _ -> _
compa (G / S) = sig \ Xs X -> sig \ Ys Y -> sig \ Zs Z -> sig \ fs f -> sig \ gs g ->
  compa G Xs Ys Zs fs gs , \ s x -> f s (g s x)

induction : {G : Cx}{O : Set}(C : O -> CON (G / O)){X : Pay G}
            (P : (o : O) -> Mu C X o -> Set) ->
            ((o : O)(xyps : [| C o |] (X , (\ o -> Sig (Mu C X o) (P o)))) ->
             P o (con (map (C o) (ida G X , konst fst) xyps))) ->
            (o : O)(y : Mu C X o) -> P o y
induction {G} C {X} P p o (con xys) =
  p o (map (C o) (ida G X , (\ o y -> (y , induction C P p o y))) xys)
