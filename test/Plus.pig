-- Let's have some natural numbers...
data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;

-- Now we can write plus like this:
let plus (m : Nat)(n : Nat) : Nat ;
refine plus m        n <= Nat.Ind m ;
refine plus 'zero    n = n ;
refine plus ('suc k) n = 'suc (plus k n) ;

-- Just to show this really works:
root ;
elab plus ('suc ('suc 'zero)) ('suc ('suc 'zero)) ;


-- Now we will prove that plus is commutative. First, some useful gadgetry...

-- Transitivity of equality:
let trans (X : Set)(a : X)(b : X)(c : X)(p : :- a == b)(q : :- b == c) : :- a == c ;
-- Well, that was easy!
root ;

-- Reversing the order of arguments to functions:
make flip := (\ f k n -> f n k) : (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat ;


-- And here come the proofs...

-- A lemma:
let plusZ (m : Nat) : :- plus m 'zero == m ;
refine plusZ m <= Nat.Ind m ;
-- This is slightly cheeky and ought to be squashed by proof search:
refine plusZ ('suc n) = plusZ n ;
root ; 

-- Another lemma:
let plusS (k : Nat)(n : Nat) : :- plus k ('suc n) == plus ('suc k) n ;
refine plusS k n <= Nat.Ind k ;
-- Again, proof search should hit this:
refine plusS ('suc j) n = plusS j n ;
root ;

-- Given some arguments, plus is commutative:
let plusComm (k : Nat)(n : Nat) : :- plus k n == plus n k ;
refine plusComm k n <= Nat.Ind n ;
refine plusComm k 'zero = plusZ k ;
refine plusComm k ('suc m) = trans Nat (plus k ('suc m)) ('suc (plus k m)) ('suc (plus m k)) (plusS k m) (plusComm k m) ;
root ;

-- We really have equality between the *functions* |plus| and |flip plus|:
make plusCommF : :- (flip plus == plus) ;
simplify ;
lambda k1, k2, p, n1, n2, q ;
<= substEq Nat k1 k2 _ ;
give plusComm n1 k1 ;
root ;