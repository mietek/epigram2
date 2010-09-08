data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;
idata Vec (A : Set) : Nat -> Set := ('cons : (n : Nat) -> (a : A) -> (as : Vec A n) -> Vec A ('suc n)) ;
let test (A : Set)(f : A -> A)(n : Nat)(x : Vec A n) : Vec A n ;
    <= Vec.Ind A n x ;
	= 'cons n^1 (f a) (test A ? n^1  as);
give f ;
