-- Let's prove substitutivity, symmetry and transitivity of equality:
make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

make sym := (\ S s t q -> ship S s t _ (\ x -> :- x == s) _) : (S : Set)(s : S)(t : S) -> :- s == t -> :- t == s ;
make trans := (\ S s t u q r -> ship S t s (sym S s t _) (\ x -> :- x == u) r) : (S : Set)(s : S)(t : S)(u : S) -> :- s == t -> :- t == u -> :- s == u ;




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
