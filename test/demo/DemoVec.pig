make Vec : Set -> Nat -> Set ;
lambda A : Set;

make VecD : Nat -> IDesc Nat _ ;
give (\ n -> 'fsigmaD ['vnil 'vcons] [ ('constD (:- ((: Nat) 'zero == n))) ('sigmaD Nat (\ m -> 'prodD ('constD A) ('prodD ('varD m) ('constD (:- ((: Nat) ('suc m) == n)))))) ]) ;

make Vec := (\ n -> IMu Nat VecD n) : Nat -> Set ;

make Ind := iinduction Nat VecD : (m : Nat)(v : Vec m)(bp : Sig (n : Nat ; Vec n) -> Set)(me : (k : Nat)(x : idesc Nat (VecD k) Vec)(hs : idesc (Sig (i : Nat ; Vec i))(ibox Nat (VecD k) Vec x) bp) -> bp [k , con x]) -> bp [m , v] ;

give Vec ;



make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;
