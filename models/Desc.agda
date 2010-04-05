{-# OPTIONS --universe-polymorphism #-}

module Desc where

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

pair : {i j : Level}{A : Set i}{B : A -> Set j} -> 
       (x : A) (y : B x) -> Sigma {i = i}{j = j} A B
pair x y = x , y

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

cong : {l m : Level}{A : Set l}{B : Set m}
       (f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong2 : {l m n : Level}{A : Set l}{B : Set m}{C : Set n}
        (f : A -> B -> C){x y : A}{z t : B} -> 
        x == y -> z == t -> f x z == f y t
cong2 f refl refl = refl

trans : {l : Level}{A : Set l}{x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

proof-lift-unlift-eq : {l : Level}{A : Set l}(x : Lifted A) -> lifter (unlift x) == x
proof-lift-unlift-eq (lifter a) = refl

postulate 
  reflFun : {l m : Level}{A : Set l}{B : A -> Set m}(f : (a : A) -> B a)(g : (a : A) -> B a)-> ((a : A) -> f a == g a) -> f == g 


--********************************************
-- Desc code
--********************************************

data Desc : Set1 where
  id : Desc
  const : Set -> Desc
  prod : Desc -> Desc -> Desc
  sigma : (S : Set) -> (S -> Desc) -> Desc
  pi : (S : Set) -> (S -> Desc) -> Desc


--********************************************
-- Desc interpretation
--********************************************

[|_|]_ : Desc -> Set -> Set
[| id |] Z        = Z
[| const X |] Z   = X
[| prod D D' |] Z = [| D |] Z * [| D' |] Z
[| sigma S T |] Z = Sigma S (\s -> [| T s |] Z)
[| pi S T |] Z    = (s : S) -> [| T s |] Z

--********************************************
-- Fixpoint construction
--********************************************

data Mu (D : Desc) : Set where
  con : [| D |] (Mu D) -> Mu D

--********************************************
-- Predicate: All
--********************************************

All : {l : Level}(D : Desc)(X : Set)(P : X -> Set l) -> [| D |] X -> Set l
All id          X P x        = P x
All (const Z)   X P x        = Unit
All (prod D D') X P (d , d') = (All D X P d) * (All D' X P d')
All (sigma S T) X P (a , b)  = All (T a) X P b
All (pi S T)    X P f        = (s : S) -> All (T s) X P (f s)


all : (D : Desc)(X : Set)(P : X -> Set)(R : (x : X) -> P x)(x : [| D |] X) -> All D X P x
all id X P R x = R x
all (const Z) X P R z = Void
all (prod D D') X P R (d , d') = all D X P R d , all D' X P R d'
all (sigma S T) X P R (a , b) = all (T a) X P R b
all (pi S T) X P R f = \ s -> all (T s) X P R (f s)

--********************************************
-- Map
--********************************************

map : (D : Desc)(X Y : Set)(f : X -> Y)(v : [| D |] X) -> [| D |] Y
map id X Y sig x = sig x
map (const Z) X Y sig z = z
map (prod D D') X Y sig (d , d') = map D X Y sig d , map D' X Y sig d'
map (sigma S T) X Y sig (a , b) = (a , map (T a) X Y sig b)
map (pi S T) X Y sig f = \x -> map (T x) X Y sig (f x)


proof-map-id : (D : Desc)(X : Set)(v : [| D |] X) -> map D X X (\x -> x) v == v
proof-map-id id X v = refl
proof-map-id (const Z) X v = refl
proof-map-id (prod D D') X (v , v') = cong2 (\x y -> (x , y)) (proof-map-id D X v) (proof-map-id D' X v')
proof-map-id (sigma S T) X (a , b) = cong (\x -> (a , x)) (proof-map-id (T a) X b) 
proof-map-id (pi S T) X f = reflFun (\a -> map (T a) X X (\x -> x) (f a)) f (\a -> proof-map-id (T a) X (f a))


proof-map-compos : (D : Desc)(X Y Z : Set)
                   (f : X -> Y)(g : Y -> Z)
                   (v : [| D |] X) -> 
                   map D X Z (\x -> g (f x)) v == map D Y Z g (map D X Y f v)
proof-map-compos id X Y Z f g v = refl
proof-map-compos (const K) X Y Z f g v = refl
proof-map-compos (prod D D') X Y Z f g (v , v') = cong2 (\x y -> (x , y)) 
                                                        (proof-map-compos D X Y Z f g v)
                                                        (proof-map-compos D' X Y Z f g v')
proof-map-compos (sigma S T) X Y Z f g (a , b) = cong (\x -> (a , x)) (proof-map-compos (T a) X Y Z f g b)
proof-map-compos (pi S T) X Y Z f g fc = reflFun (\a -> map (T a) X Z (\x -> g (f x)) (fc a))
                                                 (\a -> map (T a) Y Z g (map (T a) X Y f (fc a)))
                                                 (\a -> proof-map-compos (T a) X Y Z f g (fc a))


--********************************************
-- Elimination principle: induction
--********************************************

-- One would like to write the following:

{-
induction : (D : Desc) 
            (P : Mu D -> Set) ->
            ( (x : [| D |] (Mu D)) -> 
              All D (Mu D) P x -> P (con x)) ->
            (v : Mu D) ->
            P v
induction D P ms (con xs) = ms xs (all D (Mu D) P (\x -> induction D P ms x) xs)
-}

-- But the termination checker is unhappy.
-- So we write the following:

module Elim {l : Level}
            (D : Desc)
            (P : Mu D -> Set l)
            (ms : (x : [| D |] (Mu D)) -> 
                  All D (Mu D) P x -> P (con x))
       where

    mutual
        induction : (x : Mu D) -> P x
        induction (con xs) =  ms xs (hyps D xs)
    
        hyps : (D' : Desc)
               (xs : [| D' |] (Mu D)) ->
               All D' (Mu D) P xs
        hyps id x = induction x
        hyps (const Z) z = Void
        hyps (prod D D') (d , d') = hyps D d , hyps D' d'
        hyps (sigma S T) (a , b) = hyps (T a) b
        hyps (pi S T) f = \s -> hyps (T s) (f s)
            
induction : {l : Level}
            (D : Desc) 
            (P : Mu D -> Set l) ->
            ( (x : [| D |] (Mu D)) -> 
              All D (Mu D) P x -> P (con x)) ->
            (v : Mu D) ->
            P v
induction D P ms x = Elim.induction D P ms x


--********************************************
-- Examples
--********************************************

--****************
-- Nat
--****************

data NatConst : Set where
  Ze : NatConst
  Su : NatConst

natCases : NatConst -> Desc
natCases Ze = const Unit
natCases Suc = id

NatD : Desc
NatD = sigma NatConst  natCases

Nat : Set
Nat = Mu NatD

ze : Nat
ze = con (Ze , Void)

su : Nat -> Nat
su n = con (Su , n)

--****************
-- List
--****************

data ListConst : Set where
  Nil : ListConst
  Cons : ListConst

listCases : Set -> ListConst -> Desc
listCases X Nil = const Unit
listCases X Cons = sigma X (\_ -> id)

ListD : Set -> Desc
ListD X = sigma ListConst (listCases X)

List : Set -> Set
List X = Mu (ListD X)

nil : {X : Set} -> List X
nil = con ( Nil , Void )

cons : {X : Set} -> X -> List X -> List X
cons x t = con ( Cons , ( x , t ))

--****************
-- Tree
--****************

data TreeConst : Set where
  Leaf : TreeConst
  Node : TreeConst

treeCases : Set -> TreeConst -> Desc
treeCases X Leaf = const Unit
treeCases X Node = sigma X (\_ -> prod id id)

TreeD : Set -> Desc
TreeD X = sigma TreeConst (treeCases X)

Tree : Set -> Set
Tree X = Mu (TreeD X)

leaf : {X : Set} -> Tree X
leaf = con (Leaf , Void)

node : {X : Set} -> X -> Tree X -> Tree X -> Tree X
node x le ri = con (Node , (x , (le , ri)))


--********************************************
-- Finite sets
--********************************************

-- If we weren't such bug fans of levitating things, we would
-- implement finite sets with:

{-

data EnumU : Set where
  nilE : EnumU
  consE : EnumU -> EnumU

spi : (e : EnumU)(P : EnumT e -> Set) -> Set
spi nilE P = Unit
spi (consE e) P = P EZe * spi e (\e -> P (ESu e))

switch : (e : EnumU)(P : EnumT e -> Set)(b : spi e P)(x : EnumT e) -> P x
switch nilE P b ()
switch (consE e) P b EZe = fst b
switch (consE e) P b (ESu n) = switch e (\e -> P (ESu e)) (snd b) n
-}

-- But no, we make it fly in Desc:

EnumU : Set
EnumU = Nat

nilE : EnumU
nilE = ze

consE : EnumU -> EnumU
consE e = su e 

data EnumT : (e : EnumU) -> Set where
  EZe : {e : EnumU} -> EnumT (consE e)
  ESu : {e : EnumU} -> EnumT e -> EnumT (consE e)

-- All : {l : Level}(D : Desc)(X : Set l)(P : X -> Set l) -> [| D |] X -> Set l

{-
casesSpi : (xs : [| NatD |] Nat) -> 
           All NatD (Nat {l = zero}) (\e -> (EnumT e -> Set1) -> Set1) xs -> 
           (EnumT (con xs) -> Set1) -> Set1
casesSpi (Ze , Void) hs P' = Unit
casesSpi (Su , n) hs P' = P' EZe * hs (\e -> P' (ESu e))
-}

{-
induction : {l : Level}
            (D : Desc) 
            (P : Mu D -> Set l) ->
            ( (x : [| D |] (Mu D)) -> 
              All D (Mu D) P x -> P (con x)) ->
            (v : Mu D) ->
            P v
-}

casesSpi : (xs : [| NatD |] Nat) -> 
           All NatD Nat (\e -> (EnumT e -> Set) -> Set) xs -> 
           (EnumT (con xs) -> Set) -> Set
casesSpi (Ze , Void) hs P' = Unit
casesSpi (Su , n) hs P' = P' EZe * hs (\e -> P' (ESu e))


spi : (e : EnumU)(P : EnumT e -> Set) -> Set
spi e P =  induction NatD (\E -> (EnumT E -> Set) -> Set) casesSpi e P

{-
casesSwitch : (xs : [| NatD |] Nat) ->
              All NatD Nat (\e -> (P' : EnumT e -> Set1)
                                  (b' : spi e P')
                                  (x' : EnumT e) -> P' x') xs ->
              (P' : EnumT (con xs) -> Set1)
              (b' : spi (con xs) P')
              (x' : EnumT (con xs)) -> P' x'
casesSwitch (Ze , Void) hs P' b' ()
casesSwitch (Su , n) hs P' b' EZe = fst b'
casesSwitch (Su , n) hs P' b' (ESu e') = hs (\e -> P' (ESu e)) (snd b') e'


switch : (e : EnumU)
         (P : EnumT e -> Set1)
         (b : spi e P)
         (x : EnumT e) -> P x
switch e P b xs =  induction NatD
                            (\e -> (P : EnumT e -> Set1)
                                   (b : spi e P)
                                   (xs : EnumT e) -> P xs) 
                            casesSwitch e P b xs 


--********************************************
-- Tagged description
--********************************************

-- data Sigma {i j : Level}(A : Set i) (B : A -> Set j) : Set (max i j)
-- spi : {l : Level}(e : EnumU)(P : EnumT e -> Set l) -> Set l

TagDesc : Set2
TagDesc = Sigma (EnumU {l = suc (suc zero)}) (\e -> spi e (\_ -> Desc {l = zero}))

toDesc : {l : Level} -> TagDesc -> Desc {l = zero}
toDesc {x} (B , F) = {!!} -- sigma (EnumT B) (\e -> ?) --switch B (\_ -> Desc {l = x}) F e)

test : (E : EnumU {l = suc (suc zero)}) -> spi E (\_ -> Desc {l = zero}) -> EnumT E -> Desc {l = zero}
test B F e = {!switch B (\_ -> Desc {l = zero}) F e!}

-}
--********************************************
-- Catamorphism
--********************************************

{-

cata : (D : Desc)
       (T : Set) ->
       ([| D |] T -> T) ->
       (Mu D) -> T
cata D T phi x = induction D (\_ -> T) (\x ms -> phi (replace D T x ms)) x
  where replace : (D' : Desc)(T : Set)(xs : [| D' |] (Mu D))(ms : All D' (Mu D) (\_ -> T) xs) -> [| D' |] T
        replace id T x y = y
        replace (const Z) T z z' = z'
        replace (prod D D') T (x , x') (y , y') = replace D T x y , replace D' T x' y'
        replace (sigma A B) T (a , b) t = a , replace (B a) T b t
        replace (pi A B) T f t = \s -> replace (B s) T (f s) (t s)


--********************************************
-- Free monad construction
--********************************************

_**_ : TagDesc -> (X : Set) -> TagDesc
(e , D) ** X = consE e , (const X , D)

--********************************************
-- Substitution
--********************************************

apply : (D : TagDesc)(X Y : Set) ->
        (X -> Mu (toDesc (D ** Y))) ->
        [| toDesc (D ** X) |] (Mu (toDesc (D ** Y))) ->
        Mu (toDesc (D ** Y))
apply (E , B) X Y sig (EZe , x) = sig x
apply (E , B) X Y sig (ESu n , t) = con (ESu n , t)

subst : (D : TagDesc)(X Y : Set) ->
        Mu (toDesc (D ** X)) ->
        (X -> Mu (toDesc (D ** Y))) ->
        Mu (toDesc (D ** Y))
subst D X Y x sig = cata (toDesc (D ** X)) (Mu (toDesc (D ** Y))) (apply D X Y sig) x
-}