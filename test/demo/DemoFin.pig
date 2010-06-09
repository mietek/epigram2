make Fin : Nat -> Set ;
make FinD := (\ n -> 'fsigmaD ['fzero 'fsuc] [ ('sigmaD Nat (\ m -> 'constD (:- ((: Nat) ('suc m) == n)))) ('sigmaD Nat (\ m -> 'prodD ('varD m) ('constD (:- ((: Nat) ('suc m) == n))))) ]) : Nat -> IDesc Nat [] ;
make Fin := (\ n -> IMu Nat FinD n) : Nat -> Set ;
make Ind := iinduction Nat FinD : (m : Nat)(v : Fin m)(bp : Sig (n : Nat ; Fin n) -> Set)(me : (k : Nat)(x : idesc Nat (FinD k) Fin)(hs : idesc (Sig (i : Nat ; Fin i))(ibox Nat (FinD k) Fin x) bp) -> bp [k , con x]) -> bp [m , v] ;
give Fin ;


make nuffin : Fin 'zero -> :- FF ;
lambda x ;
elim Fin.Ind 'zero x ;
lambda k ;
give con [? ?] ;
give con \ n q -> ? ;
<= ship Nat ('suc n) k q ;
give con \ n -> con \ v q -> ? ;
<= ship Nat ('suc n) k q ;
root ;