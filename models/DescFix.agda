{-# OPTIONS --type-in-type #-}

module DescFix where

open import DescTT


aux : (C : Desc)(D : Desc)(P : Mu C -> Set)(x : [| D |] (Mu C)) -> Set
aux C id          P (con y) = P (con y) * aux C C P y 
aux C (const K)   P k       = Unit
aux C (prod D D') P (s , t) = aux C D P s * aux C D' P t
aux C (sigma S T) P (s , t) = aux C (T s) P t
aux C (pi S T)    P f       = (s : S) -> aux C (T s) P (f s)


gen : (C : Desc)(D : Desc)(P : Mu C -> Set)
  (rec : (y : [| C |] Mu C) -> aux C C P y -> P (con y))
  (x : [| D |] Mu C) -> aux C D P x
gen C id          P rec (con x) = rec x (gen C C P rec x) , gen C C P rec x
gen C (const K)   P rec k       = Void
gen C (prod D D') P rec (s , t) = gen C D P rec s , gen C D' P rec t
gen C (sigma S T) P rec (s , t) = gen C (T s) P rec t
gen C (pi S T)    P rec f       = \ s -> gen C (T s) P rec (f s)


fix : (D : Desc)(P : Mu D -> Set)
  (rec : (y : [| D |] Mu D) -> aux D D P y -> P (con y))
  (x : Mu D) -> P x
fix D P rec (con x) = rec x (gen D D P rec x)



plus : Nat -> Nat -> Nat
plus (con (Ze , Void)) n = n
plus (con (Suc , m)) n = suc (plus m n)

fib : Nat -> Nat
fib = fix NatD (\ _ -> Nat) help
  where
    help : (m : [| NatD |] Nat) -> aux NatD NatD (\ _ -> Nat) m -> Nat
    help (Ze , x) a = suc ze
    help (Suc , con (Ze , _)) a = suc ze
    help (Suc , con (Suc , con n)) (fib-n , (fib-sn , a)) = plus fib-n fib-sn