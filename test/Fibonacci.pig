-- Let's prove substitutivity, symmetry and transitivity of equality:
make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

make sym := (\ S s t q -> ship S s t _ (\ x -> :- x == s) _) : (S : Set)(s : S)(t : S) -> :- s == t -> :- t == s ;
make trans := (\ S s t u q r -> ship S t s (sym S s t _) (\ x -> :- x == u) r) : (S : Set)(s : S)(t : S)(u : S) -> :- s == t -> :- t == u -> :- s == u ;


-- Now we need natural numbers, their case analysis principle and addition:
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


-- We are going to build the recursion principle for natural numbers.

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
= _ ;
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
<= [xf] NatCase k ;
= 'suc 'zero ;
<= [xf] NatCase xf^2 ;
= 'suc 'zero ;

-- Unfortunately, our implementation of elimination with a motive is currently
-- unable to simplify the hypothesis, so we have to extract the justification
-- for the recursive calls by hand. 
make rec := ship Nat k ('suc ('suc xf^1)) ? (aux P^2) xf^5 : _ ;
next ;
give trans Nat k ('suc xf^6) ('suc ('suc xf^1)) ? ? ;
give sym Nat ('suc xf^6) k xf^4 ;
give sym Nat ('suc xf^1) xf^6 xf ;
out ;
out ;

-- Having done that, we can make the recursive call. We need a blunderbuss to
-- deal with finding the labelled types!
= plus (fib xf^1) (fib ('suc xf^1)) ;
give rec - ! ;
give rec ! ;

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