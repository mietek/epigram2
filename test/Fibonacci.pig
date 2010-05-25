-- We are going to build the recursion principle for natural numbers.
-- We need to define the natural numbers, their case analysis principle and
-- addition:
data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

make NatCase : (n : Nat)(P : Nat -> Set)(p : (x : desc Nat.DataDesc Nat) -> P (con x)) -> P n ;
lambda n, P, p ;
give Nat.Ind n P (\ x _ -> p x) ;
root ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus xf^1 n) ;
root ;


-- We need an auxiliary structure to memoise results of computation; this is a
-- predicate transformer that means P holds below n.
let aux (P : Nat -> Set)(n : Nat) : Set ;
<= Nat.Ind n ;
= Sig () ;
= Sig (P xf^1 ; aux P xf^1) ;
root ;

-- We can build such a structure if we can get P k from the P j for j < k:
let aux-gen (P : Nat -> Set)(r : (k : Nat) -> aux P k -> P k)(n : Nat) : aux P n ;
<= [n] Nat.Ind n ;
= [? , ?] ;
give r xf^1 (aux-gen P^1 r xf^1) ;
give aux-gen P^1 r xf^1 ;
root ;

-- Now the recursion principle is just a minor modification:
make NatRec := (\ n P r -> r n (aux-gen P r n)) : (n : Nat)(P : Nat -> Set)(r : (k : Nat) -> aux P k -> P k) -> P n ;


-- Let's use NatRec to simulate rabbit population growth.

-- The Fibonacci function is defined by recursion and case analysis (twice):
let fib (n : Nat) : Nat ;
<= NatRec n ;
<= NatCase k ;
= 'suc 'zero ;
<= NatCase xf^2 ;
= 'suc 'zero ;
= plus (fib xf^4) (fib ('suc xf^4)) ;
root ;

-- Hooray, fib is defined and we can go ahead and count the rabbits:
elab fib 'zero ;
elab fib ('suc 'zero) ;
elab fib ('suc ('suc 'zero)) ;
elab fib ('suc ('suc ('suc 'zero))) ;
elab fib ('suc ('suc ('suc ('suc 'zero)))) ;
elab fib ('suc ('suc ('suc ('suc ('suc 'zero))))) ;
elab fib ('suc ('suc ('suc ('suc ('suc ('suc 'zero)))))) ;
elab fib ('suc ('suc ('suc ('suc ('suc ('suc ('suc 'zero))))))) ;