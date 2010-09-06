data Nat := 
      (zero : Nat) 
    ; (suc : Nat -> Nat) ;
idata Vec (A : Set) : Nat -> Set := 
    (cons : (n : Nat) -> A -> Vec A n -> Vec A ('suc n)) ;

let testNOTOK (A : Set)(f : A -> A)(n : Nat)(x : Vec A n) : Vec A n ;
    <= Vec.Ind A n x ;
	= 'cons  s^2 (f s) (testNOTOK A ? s^2  xf^1);
