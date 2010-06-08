make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;

make NatF : :- TT -> Set ;

make NatD := (\ _ -> 'fsigmaD ['zero 'suc] [ ('constD (:- TT)) ('prodD ('varD _) ('constD (:- TT))) ]) : (:- TT) -> IDesc (:- TT) [] ;
lambda v ;
give IMu (:- TT) NatD v ;

make Nat := NatF _ : Set ;

make one := 'suc 'zero : Nat ;
make two := 'suc one : Nat ;

make Fin : Nat -> Set ;
lambda n ;
give IMu Nat (\ n -> 'fsigmaD ['fzero 'fsuc] [ ('sigmaD Nat (\ m -> 'constD (:- ((: Nat) ('suc m) == n)))) ('sigmaD Nat (\ m -> 'prodD ('varD m) ('constD (:- ((: Nat) ('suc m) == n))))) ]) n ;

make foo := (\ m n q -> ship Nat ('suc m) n q Fin ('fzero m)) : (m : Nat) -> (n : Nat) -> (:- ((: Nat) ('suc m) == n)) -> Fin n ; 
make bar := (\ m n i q -> ship Nat ('suc m) n q Fin ('fsuc m i)) : (m : Nat) -> (n : Nat) -> Fin m -> (:- ((: Nat) ('suc m) == n)) -> Fin n ; 
