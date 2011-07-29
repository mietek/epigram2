{-# OPTIONS --universe-polymorphism #-}

module LLev where

--****************
-- Universe polymorphism
--****************

data Level : Set where
      ze : Level
      su  : Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO ze  #-}
{-# BUILTIN LEVELSUC  su   #-}

max : Level -> Level -> Level
max  ze     m     = m
max (su n)  ze    = su n
max (su n) (su m) = su (max n m)

{-# BUILTIN LEVELMAX max #-}

record Up {l : Level} (A : Set l) : Set (su l) where
  constructor up
  field down : A
open Up

record Sg {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : {l : Level} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T
infixr 4 _*_ _,_

data Zero : Set where

record One {l : Level} : Set l where
  constructor <>

data Desc {l : Level}(I : Set l) : Set (su l) where
  var : (i : I) -> Desc I
  con : (A : Set l) -> Desc I
  sg pi : (S : Set l)(T : S -> Desc I) -> Desc I
  _**_ : (S T : Desc I) -> Desc I
infixr 4 _**_

[!_!] : {l : Level}{I : Set l} -> Desc I -> (I -> Set l) -> Set l
[! var i !] X = X i
[! con A !] X = A
[! sg S T !] X = Sg S \ s -> [! T s !] X
[! pi S T !] X = (s : S) -> [! T s !] X
[! S ** T !] X = [! S !] X * [! T !] X

{-
data Mu {l : Level}(I : Set l)(F : I -> Desc I)(i : I) : Set l where
  <_> : [! F i !] (Mu I F) -> Mu I F i
-}

All : {l : Level}{I : Set l}
      (D : Desc I)(X : I -> Set l) -> [! D !] X -> Desc (Sg I X)
All (var i) X x = var (i , x)
All (con A) X d = con One
All (sg S T) X (s , t) = All (T s) X t
All (pi S T) X f = pi S \ s -> All (T s) X (f s)
All (S ** T) X (s , t) = All S X s ** All T X t

all : {l : Level}{I : Set l}
      (D : Desc I)(X : I -> Set l)(P : Sg I X -> Set l) ->
      ((ix : Sg I X) -> P ix) ->
      (d : [! D !] X) -> [! All D X d !] P
all (var i) X P p x = p (i , x)
all (con A) X P p d = _
all (sg S T) X P p (s , t) = all (T s) X P p t
all (pi S T) X P p f = \ s -> all (T s) X P p (f s)
all (S ** T) X P p (s , t) = all S X P p s , all T X P p t

{-
induction :  {l : Level}{I : Set l}{F : I -> Desc I}
             (P : Sg I (Mu I F) -> Set l) ->
             ((i : I)(d : [! F i !] (Mu I F)) ->
               [! All (F i) (Mu I F) d !] P -> P (i , < d >)) ->
             (ix : Sg I (Mu I F)) -> P ix
induction {F = F} P p (i , < d >) = p i d (all (F i) (Mu _ F) P (induction P p) d)
-}

{-
mutual
  induction :  {l : Level}{I : Set l}{F : I -> Desc I}
               (P : Sg I (Mu I F) -> Set l) ->
               ((i : I)(d : [! F i !] (Mu I F)) ->
                 [! All (F i) (Mu I F) d !] P -> P (i , < d >)) ->
               {i : I}(x : Mu I F i) -> P (i , x)
  induction {F = F} P p {i} < d > = p i d (allInduction F P p (F i) d)
  allInduction : {l : Level}{I : Set l}(F : I -> Desc I)
                 (P : Sg I (Mu I F) -> Set l) ->
                 ((i : I)(d : [! F i !] (Mu I F)) ->
                    [! All (F i) (Mu I F) d !] P -> P (i , < d >)) ->
                 (D : Desc I) ->
                 (d : [! D !] (Mu I F)) -> [! All D (Mu I F) d !] P
  allInduction F P p (var i) d = induction P p d
  allInduction F P p (con A) d = _
  allInduction F P p (sg S T) (s , t) = allInduction F P p (T s) t
  allInduction F P p (pi S T) f = \ s -> allInduction F P p (T s) (f s)
  allInduction F P p (S ** T) (s , t) = allInduction F P p S s , allInduction F P p T t
-}

data List {l : Level}(X : Set l) : Set l where
  [] : List X
  _::_ : X -> List X -> List X
infixr 3 _::_

map : {k l : Level}{X : Set k}{Y : Set l} -> (X -> Y) -> List X -> List Y
map f [] = []
map f (x :: xs) = f x :: map f xs

data UId {l : Level} : Set l where
  ze : UId
  su : UId {l} -> UId

data # {l : Level} : List {l} UId -> Set l where
  ze : forall {x xs} -> # (x :: xs)
  su : forall {x xs} -> # xs -> # (x :: xs)

Constrs : {l : Level} -> Set l -> Set (su l)
Constrs I = List (Up UId * Desc I)

Constr : {l : Level}{I : Set l} -> Constrs I -> Set l
Constr uDs = # (map (\ uD -> down (fst uD)) uDs)

ConD : {l : Level}{I : Set l}(uDs : Constrs I) -> Constr uDs -> Desc I
ConD [] ()
ConD (uD :: _)  ze     = snd uD
ConD (_ :: uDs) (su c) = ConD uDs c

data Data {l : Level}{I : Set l}(F : I -> Constrs I)(i : I) : Set l where
  _/_ : (u : Constr (F i))(d : [! ConD (F i) u !] (Data F)) -> Data F i

{-
DataD : {l : Level}{I : Set l} -> Constrs I -> Desc I
DataD uDs = sg (Constr uDs) (ConD uDs)

Data : {l : Level}{I : Set l}(F : I -> Constrs I)(i : I) -> Set l
Data F = Mu _ \ i -> DataD (F i)
-}

MethodD : {l : Level}{I : Set l}(X : I -> Set l)
          (uDs : Constrs I)
          (P : Sg I X -> Set l)
          (i : I) -> ((u : Constr uDs)(d : [! ConD uDs u !] X) -> X i) -> Set l
MethodD X [] P i c = One
MethodD X ((u , D) :: uDs) P i c
  = ((d : [! D !] X) -> [! All D X d !] P -> P (i , c ze d))
  * MethodD X uDs P i (\ u d -> c (su u) d)

mutual
  induction : {l : Level}{I : Set l}{F : I -> Constrs I}{i : I}(x : Data F i) 
              (P : Sg I (Data F) -> Set l)
              (ps : (i : I) -> MethodD (Data F) (F i) P i _/_)
              -> P (i , x)
  induction {F = F}{i = i}(u / d) P ps = indMethod P ps (F i) _/_ (ps i) u d
  indMethod : {l : Level}{I : Set l}{F : I -> Constrs I}{i : I}
              (P : Sg I (Data F) -> Set l)
              (ps : (i : I) -> MethodD (Data F) (F i) P i _/_)
              (uDs : Constrs I)
              (c : (u : Constr uDs) -> [! ConD uDs u !] (Data F) -> Data F i)
              (ms : MethodD (Data F) uDs P i c)
              (u : Constr uDs)
              (d : [! ConD uDs u !] (Data F))
              -> P (i , c u d)
  indMethod P ps [] c ms () d
  indMethod P ps ((u , D) :: _) c (p , ms) ze d = p d (indHyps P ps D d)
  indMethod P ps ((_ , _) :: uDs) c (m , ms) (su u) d
    = indMethod P ps uDs _ ms u d
  indHyps : {l : Level}{I : Set l}{F : I -> Constrs I}
            (P : Sg I (Data F) -> Set l)
            (ps : (i : I) -> MethodD (Data F) (F i) P i _/_)
            (D : Desc I)
            (d : [! D !] (Data F))
            -> [! All D (Data F) d !] P
  indHyps P ps (var i) x = induction x P ps
  indHyps P ps (con A) a = _
  indHyps P ps (sg S T) (s , t) = indHyps P ps (T s) t
  indHyps P ps (pi S T) f = \ s -> indHyps P ps (T s) (f s)
  indHyps P ps (S ** T) (s , t) = indHyps P ps S s , indHyps P ps T t

zi : {l : Level} -> UId {l}
zi = ze

si : {l : Level} -> UId {l}
si = su ze

data UQ {l : Level}(x : UId {l}) : UId {l} -> Set l where
  yes : UQ x x
  no  : {y : UId {l}} -> UQ x y

uq : {l : Level}(x y : UId {l}) -> UQ x y
uq ze ze = yes
uq ze (su y) = no
uq (su x) ze = no
uq (su x) (su y) with uq x y
uq (su x) (su .x) | yes = yes
uq (su x) (su y)  | no  = no

UIn : {l : Level}(x : UId {l}) -> List (UId {l}) -> Set
UIn x [] = Zero
UIn x (y :: ys) with uq x y
UIn x (.x :: _) | yes = One
UIn x (_ :: ys) | no = UIn x ys

uin : {l : Level}(x : UId {l})(ys : List (UId {l})) -> UIn x ys -> # ys
uin x [] ()
uin x (y :: ys) p with uq x y
uin x (.x :: _) _ | yes = ze
uin x (_ :: ys) p | no  = su (uin x ys p)

_!_ : {l : Level}{I : Set l}{F : I -> Constrs I}{i : I} ->
      let us = map (\ uD -> down (fst uD)) (F i) in
      (u : UId {l}){p : UIn u us} ->
      [! ConD (F i) (uin u us p) !] (Data F) ->
      Data F i
_!_ {l}{I}{F}{i} u {p} d = uin u (map (\ uD -> down (fst uD)) (F i)) p / d

infixr 3 _!_


NAT : {l : Level} -> One {l} -> Constrs {l} One
NAT _ = up zi , con One 
     :: up si , var _ ** con One
     :: []

ZE : {l : Level} -> Data {l} NAT <>
ZE = zi ! <>

SU : {l : Level} -> Data {l} NAT <> -> Data {l} NAT <>
SU n = si ! n , <>

vari : {l : Level} -> UId {l}
vari = ze
coni : {l : Level} -> UId {l}
coni = su ze
sgi : {l : Level} -> UId {l}
sgi = su (su ze)
pii : {l : Level} -> UId {l}
pii = su (su (su ze))
asti : {l : Level} -> UId {l}
asti = su (su (su (su ze)))

DESC : {l : Level}(I : Set l) -> One {su l} -> Constrs {su l} One
DESC I _ = up vari , con (Up I) ** con One
        :: up coni , con (Set _) ** con One
        :: up sgi , (sg (Set _) \ S -> (pi (Up S) \ _ -> var _) ** con One)
        :: up pii , (sg (Set _) \ S -> (pi (Up S) \ _ -> var _) ** con One)
        :: up asti , var _ ** var _ ** con One
        :: []
