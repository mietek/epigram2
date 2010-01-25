make ship := (\ X x y q P p ->
               coe(P x, P y, con (((: :- P == P) [])
                                % x y []), p))
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
make Bool := (Enum ['true 'false]) : Set ;
make So : Bool -> Set ;
lambda b ;
give IMu Bool (\ b -> IDone (((: Bool) 'true) == b)) b ;
make oh := con [] : So 'true ;
make NatF : :- TT -> Set ;
make NatD := (\ _ -> IArg (Enum ['zero 'suc]) [ (IDone TT) (IInd1 [] (IDone TT)) ]) : (:- TT) -> IDesc (:- TT) ;
lambda v ;
give IMu (:- TT) NatD v ;
make Nat := NatF [] : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make Fin : Nat -> Set ;
lambda n ;
give IMu Nat (\ n -> IArg (Enum ['zero 'suc]) [ (IArg Nat (\ m -> IDone (suc m == n))) (IArg Nat (\ m -> IInd1 m (IDone (suc m == n)))) ]) n ;
make fzero := (\ m -> con ['zero m]) : (m : Nat) -> Fin (suc m) ; 
make fsuc := (\ m i -> con ['suc m i]) : (m : Nat) -> Fin m -> Fin (suc m) ;
make foo := (\ m n q -> ship Nat (suc m) n q Fin (fzero m)) : (m : Nat) -> (n : Nat) -> (:- (suc m == n)) -> Fin n ; 
make bar := (\ m n i q -> ship Nat (suc m) n q Fin (fsuc m i)) : (m : Nat) -> (n : Nat) -> Fin m -> (:- (suc m == n)) -> Fin n ; 
