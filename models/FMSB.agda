module FMSB where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Lam (X : Nat -> Set)(n : Nat) : Set where
  var : X n -> Lam X n
  app : Lam X n -> Lam X n -> Lam X n
  lam : Lam X (su n) -> Lam X n

_->>_ : {I : Set}(X Y : I -> Set) -> Set
X ->> Y = {i : _} -> X i -> Y i

fmsub : {X Y : Nat -> Set} -> (X ->> Lam Y) -> Lam X ->> Lam Y
fmsub sb (var x)   = sb x
fmsub sb (app f s) = app (fmsub sb f) (fmsub sb s)
fmsub sb (lam b)   = lam (fmsub sb b)

data Fin : Nat -> Set where
  ze : {n : Nat} -> Fin (su n)
  su : {n : Nat} -> Fin n -> Fin (su n)

D : (Nat -> Set) -> Nat -> Set
D F n = F (su n)

weak : {F : Nat -> Set} -> (Fin ->> F) -> (F ->> D F) ->
       {m n : Nat}-> (Fin m -> F n) -> D Fin m -> D F n
weak v w f ze      = v ze
weak v w f (su x)  = w (f x)

_+_ : Nat -> Nat -> Nat
ze    + y = y
su x  + y = su (x + y)

_!+_ : (Nat -> Set) -> Nat -> (Nat -> Set)
F !+ n = \ m -> F (m + n)

weaks : {F : Nat -> Set} -> (Fin ->> F) -> (F ->> D F) ->
        {m n : Nat}-> (Fin m -> F n) -> (Fin !+ m) ->> (F !+ n)
weaks v w f {ze}    = f
weaks v w f {su i}  = weak v w (weaks v w f {i})

jing : {m n : Nat} -> Lam Fin (m + n) -> Lam (Fin !+ n) m
jing (var x) = var x
jing (app f s) = app (jing f) (jing s)
jing (lam t) = lam (jing t)

gnij : {m n : Nat} -> Lam (Fin !+ n) m -> Lam Fin (m + n)
gnij (var x) = var x
gnij (app f s) = app (gnij f) (gnij s)
gnij (lam t) = lam (gnij t)

ren : {m n : Nat} -> (Fin m -> Fin n) -> Lam Fin m -> Lam Fin n
ren f t = gnij (fmsub (\ {i} x -> var (weaks (\ z -> z) su f {i} x)) {ze} (jing t))

sub : {m n : Nat} -> (Fin m -> Lam Fin n) -> Lam Fin m -> Lam Fin n
sub {m}{n} f t = gnij {ze} (fmsub (\ {i} x -> jing {i} (weaks {Lam Fin} var (ren su) f {i} x)) (jing {ze} t))