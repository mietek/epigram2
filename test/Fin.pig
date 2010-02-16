make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
make NatF : :- TT -> Set ;
make NatD := (\ _ -> IArg (Enum ['zero 'suc]) [ (IDone TT) (IInd1 _ (IDone TT)) ]) : (:- TT) -> IDesc (:- TT) ;
lambda v ;
give IMu (:- TT) NatD v ;
make Nat := NatF _ : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make Fin : Nat -> Set ;
lambda n ;
give IMu Nat (\ n -> IArg (Enum ['zero 'suc]) [ (IArg Nat (\ m -> IDone (suc m == n))) (IArg Nat (\ m -> IInd1 m (IDone (suc m == n)))) ]) n ;
make fzero := (\ m -> con ['zero m, _]) : (m : Nat) -> Fin (suc m) ; 
make fsuc := (\ m i -> con ['suc m i, _]) : (m : Nat) -> Fin m -> Fin (suc m) ;
make foo := (\ m n q -> ship Nat (suc m) n q Fin (fzero m)) : (m : Nat) -> (n : Nat) -> (:- (suc m == n)) -> Fin n ; 
make bar := (\ m n i q -> ship Nat (suc m) n q Fin (fsuc m i)) : (m : Nat) -> (n : Nat) -> Fin m -> (:- (suc m == n)) -> Fin n ; 
