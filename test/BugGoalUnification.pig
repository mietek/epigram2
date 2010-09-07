data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;
idata Vec (A : Set) : Nat -> Set := (cons : (n : Nat) -> A -> Vec A n -> Vec A ('suc n)) ;
let test (A : Set)(f : A -> A)(n : Nat)(x : Vec A n) : Vec A n ;
    <= Vec.Ind A n x ;
	= 'cons  s^2 (f s) (test A ? s^2  xf^1);
give f ;