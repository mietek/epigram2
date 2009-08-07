{-# OPTIONS --type-in-type --no-termination-check
 #-}

module Data where

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

data Two : Set where
  tt : Two
  ff : Two

cond : {S : Two -> Set} -> S tt -> S ff -> (b : Two) -> S b
cond t f tt = t
cond t f ff = f

_+_ : Set -> Set -> Set
S + T = Sig Two (cond S T)

[_,_] : {S T : Set}{P : S + T -> Set} ->
        ((s : S) -> P (tt , s)) -> ((t : T) -> P (ff , t)) ->
        (x : S + T) -> P x
[ f , g ] = sig (cond f g)

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

data CON (I : Set) : Set where
  ?? : I -> CON I
  PrfC : PROP -> CON I
  _*C_ : CON I -> CON I -> CON I
  PiC : (S : Set) -> (S -> CON I) -> CON I
  SiC : (S : Set) -> (S -> CON I) -> CON I
  MuC : (O : Set) -> (O -> CON (I + O)) -> O -> CON I
  NuC : (O : Set) -> (O -> CON (I + O)) -> O -> CON I

mutual
  [|_|] : {I : Set} -> CON I -> (I -> Set) -> Set
  [| ?? i |]       X = X i
  [| PrfC P |]     X = Prf P
  [| C *C D |]     X = [| C |] X * [| D |] X
  [| PiC S C |]    X = (s : S) -> [| C s |] X
  [| SiC S C |]    X = Sig S \ s -> [| C s |] X
  [| MuC O C o |]  X = Mu C X o
  [| NuC O C o |]  X = Nu C X o

  data Mu {I O : Set}(C : O -> CON (I + O))(X : I -> Set)(o : O) : Set where
    con : [| C o |] [ X , Mu C X ] -> Mu C X o
  codata Nu {I O : Set}(C : O -> CON (I + O))(X : I -> Set)(o : O) : Set where
    con : [| C o |] [ X , Nu C X ] -> Nu C X o

noc :  {I O : Set}{C : O -> CON (I + O)}{X : I -> Set}{o : O} ->
       Nu C X o -> [| C o |] [ X , Nu C X ]
noc (con xs) = xs

mutual
  map : {I : Set}{X Y : I -> Set} -> (C : CON I) -> ((i : I) -> X i -> Y i) ->
        [| C |] X -> [| C |] Y
  map (?? i)       f = f i
  map (PrfC P)     f = id
  map (C *C D)     f = sig \ c d -> map C f c , map D f d
  map (PiC S C)    f = \ c s -> map (C s) f (c s)
  map (SiC S C)    f = sig \ s c -> s , map (C s) f c
  map (MuC O C o)  f = fold C (Mu C _) (\ o xs -> con (map (C o) [ f , konst id ] xs)) o
  map (NuC O C o)  f = unfold C (Nu C _) (\ o ss -> map (C o) [ f , konst id ] (noc ss)) o

  fold :  {I O : Set}(C : O -> CON (I + O)){X : I -> Set}(Y : O -> Set) ->
          ((o : O) -> [| C o |] [ X , Y ] -> Y o) ->
          (o : O) -> Mu C X o -> Y o
  fold C Y f o (con xs) = f o (map (C o) [ konst id , fold C Y f ] xs)

  unfold :  {I O : Set}(C : O -> CON (I + O)){X : I -> Set}(Y : O -> Set) ->
            ((o : O) -> Y o -> [| C o |] [ X , Y ]) ->
            (o : O) -> Y o -> Nu C X o
  unfold C Y f o y = con (map (C o) [ konst id , unfold C Y f ] (f o y))

induction : {I O : Set}(C : O -> CON (I + O)){X : I -> Set}
            (P : (o : O) -> Mu C X o -> Set) ->
            ((o : O)(xyps : [| C o |] [ X , (\ o -> Sig (Mu C X o) (P o)) ]) ->
             P o (con (map (C o) [ konst id , konst fst ] xyps))) ->
            (o : O)(y : Mu C X o) -> P o y
induction C P p o (con xys) =
  p o (map (C o) [ konst id , (\ o y -> (y , induction C P p o y)) ] xys)


moo : {I O : Set}(C : O -> CON (I + O)){X : I -> Set}(o : O)
      (W : (o : O) -> Mu C X o -> Set)(w : (o : O)(y : Mu C X o) -> W o y)
      (P : (io : I + O) -> [| ?? io |] [ X , Mu C X ] -> Set)
      (io : I + O)(xy : [| ?? io |] [ X , Mu C X ]) -> P io xy ->
      let g : (io : I + O) ->
              [| ?? io |] [ X , Mu C X ] -> [| ?? io |] [ X , (\ o -> Sig (Mu C X o) (W o)) ]
          g = [ konst id , (\ o y -> (y , w o y)) ]
          f : (io : I + O) ->
              [| ?? io |] [ X , (\ o -> Sig (Mu C X o) (W o)) ] -> [| ?? io |] [ X , Mu C X ]
          f = [ konst id , konst fst ]
      in  P io (f io (g io xy))
moo C o W w P io xy p = {!p!}

