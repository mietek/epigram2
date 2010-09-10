data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;
idata Vec (A : Set) : Nat -> Set := ('cons : (n : Nat) -> (a : A) -> (as : Vec A n) -> Vec A ('suc n)) ;
let test (A : Set)(f : A -> A)(n : Nat)(x : Vec A n) : Vec A n ;
    <= Vec.Ind A n x ;
	refine test A f ('suc n) ('cons n a as) = 'cons n (f a) (test A ? n as);
give f ;
