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

data _==_ {X : Set}(x : X) : {Y : Set} -> Y -> Set where
  refl : x == x

subst : {X : Set}{P : X -> Set}{x y : X} -> x == y -> P x -> P y
subst refl p = p

_=,=_ : {S : Set}{T : S -> Set}
        {s0 : S}{s1 : S} -> s0 == s1 ->
        {t0 : T s0}{t1 : T s1} -> t0 == t1 ->
        _==_ {Sig S T} (s0 , t0) {Sig S T} (s1 , t1)
refl =,= refl = refl
        

mylem :  (G : Cx) -> (X : Pay G) -> compa G X X X (ida G X) (ida G X) == ida G X
mylem E X = refl
mylem (G / S) X = mylem G (fst X) =,= refl

claim : (G : Cx){O : Set}(C : O -> CON (G / O))(X : Pay G)
        (P : (o : O) -> Mu C X o -> Set) -> (p : (o : O)(y : Mu C X o) -> P o y)
        (o : O) ->
        compa (G / O) (X , Mu C X) (X , (\ o -> Sig (Mu C X o) (P o))) (X , Mu C X)
         (ida G X , konst fst) (ida G X , (\ o y -> (y , p o y)))
        == ida (G / O) (X , Mu C X)
claim G C X P p o = mylem G X =,= refl

idLem : {G : Cx}{S : Set}{X : Pay G}(n : G :> S) ->
        pr (ida G X) n == (\ (s : S)(x : pr X n s) -> x)
idLem ze = refl
idLem (su y) = idLem y

_=$_ : {S : Set}{T : S -> Set}{f g : (s : S) -> T s} ->
        f == g -> (s : S) -> f s == g s
refl =$ s = refl

mutual  -- and too intensional
  mapId : {G : Cx}{X : Pay G} -> (C : CON G) -> (xs : [| C |] X) ->
          map C (ida G X) xs == xs
  mapId (?? y y') xs = (idLem y =$ y') =$ xs
  mapId (PrfC y) xs = refl
  mapId (y *C y') xs = mapId y (fst xs) =,= mapId y' (snd xs)
  mapId (PiC S y) xs = {!!} -- no chance
  mapId (SiC S y) xs = refl =,= mapId (y (fst xs)) (snd xs)
  mapId (MuC O y y') xs = foldMapId y y' xs
  mapId (NuC O y y') xs = {!!}

  foldMapId : {G : Cx}{O : Set}(C : O -> CON (G / O)){X : Pay G}
              (o : O)(z : Mu C X o) ->
              foldMap C (Mu C X) (ida G X) (\ o -> con) o z == z
  foldMapId C o (con xzs) = {!!} -- close but no banana

mapComp :  {G : Cx}{X Y Z : Pay G} (f : Arr G Y Z)(g : Arr G X Y)
           (C : CON G) -> (xs : [| C |] X) ->
           map C f (map C g xs) == map C (compa G X Y Z f g) xs
mapComp = {!!}


_-=-_ : {X : Set}{x y z : X} -> x == y -> y == z -> x == z
refl -=- refl = refl

induction : {G : Cx}{O : Set}(C : O -> CON (G / O)){X : Pay G}
            (P : (o : O) -> Mu C X o -> Set) ->
            ((o : O)(xyps : [| C o |] (X , (\ o -> Sig (Mu C X o) (P o)))) ->
             P o (con (map (C o) (ida G X , konst fst) xyps))) ->
            (o : O)(y : Mu C X o) -> P o y
induction {G} C {X} P p o (con xys) =
  subst {P = \ xys -> P o (con xys)}{y = xys}
    ((mapComp 
     (ida G X , konst fst) (ida G X , (\ o y -> (y , induction C P p o y))) (C o) xys
     -=- {!!}) 
      -=- mapId (C o) xys)
    (p o (map (C o) (ida G X , (\ o y -> (y , induction C P p o y))) xys))
