-- Let's have some natural numbers...
data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

-- Now we can write plus like this:
let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
-- Sorry about the terrible name choice!
= Nat.suc (plus xf^1 n) ;

-- Just to show this really works:
root ;
elab plus (Nat.suc (Nat.suc Nat.zero)) (Nat.suc (Nat.suc Nat.zero)) ;

-- And some proofs:
make plusZ : (m : Nat) -> :- plus m Nat.zero == m ;
lambda m ;
<= Nat.Ind m ;
root ; 

make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

make plzq : :- (((: Nat -> Nat) \ x -> plus x Nat.zero) == plus Nat.zero) ;
give con ? ;
lambda m, n, q ;
give ship Nat m n _ (\ y -> :- plus m Nat.zero == y) (plusZ m) % ;