-- Let's have some natural numbers...
data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

-- ...and their induction principle.
make NatInd := induction Nat.DataDesc : (v : Nat)(P : Nat -> Set)(p : (x : desc Nat.DataDesc Nat) -> box Nat.DataDesc Nat P x -> P (con x)) -> P v ;

-- Now we can write plus like this:
let plus (m : Nat)(n : Nat) : Nat ;
<= NatInd m ;
= n ;
-- Sorry about the terrible name choice!
= Nat.suc (plus xf^1 n) ;

-- Just to show this really works:
root ;
elab plus (Nat.suc (Nat.suc Nat.zero)) (Nat.suc (Nat.suc Nat.zero)) ;