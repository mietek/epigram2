-- We are going to build the recursion principle for natural numbers.
-- We need to define the natural numbers, their case analysis principle and
-- addition:
data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;

make NatCase : (n : Nat)(P : (n : Nat) -> Set)(p : (nt : desc Nat.DataDesc Nat) -> P (con nt)) -> P n ;
lambda n, P, p ;
give Nat.Ind n P (\ x _ -> p x) ;
root ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus n^1 n) ;
root ;


-- We need an auxiliary structure to memoise results of computation; this is a
-- predicate transformer that means P holds below n.
let aux (P : Nat -> Set)(n : Nat) : Set ;
<= Nat.Ind n ;
= Sig () ;
= Sig (np : P n ; aux P n) ;
root ;

-- We can build such a structure if we can get P k from the P j for j < k:
let aux-gen (n : Nat)(P : Nat -> Set)(nr : (n : Nat) -> aux P n -> P n) : aux P n ;
<= Nat.Ind n ;
= [? , ?] ;
give nr n (aux-gen n P nr) ;
give aux-gen n P nr ;
root ;

-- Now the recursion principle is just a minor modification:
make NatRec := (\ n P m -> m n (aux-gen n P m)) : (n : Nat)(P : (n : Nat) -> Set)(m : (n : Nat) -> (nrec : aux P n) -> P n) -> P n ;


-- Let's use NatRec to simulate rabbit population growth.

-- The Fibonacci function is defined by recursion and case analysis (twice):
let fib (n : Nat) : Nat ;
<= NatRec n ;
<= NatCase n ;
define fib 'zero := 'suc 'zero ;
relabel fib ('suc m) ;
<= NatCase m ;
define fib ('suc 'zero) := 'suc 'zero ;
define fib ('suc ('suc k)) := plus (fib k) (fib ('suc k)) ;
-- there seem to be too many Nats in the context, for why?
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
