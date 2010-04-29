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