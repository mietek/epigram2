load TaggedInduction.pig;

data Nat := ('zero : Nat)
          ; ('suc  : Nat -> Nat);

idata Fin : Nat -> Set := ('fz : (n : Nat) -> Fin ('suc n))
     	               ; ('fs : (n : Nat)(i : Fin n) -> Fin ('suc n));

idata Leq : Sig (n : Nat; Fin n ; Fin n; ) -> Set 
      := ('leqz : (n : Nat)(j : Fin ('suc n)) -> 
      	 	  Leq [('suc n) ('fz n) j])
       ; ('leqs : (n : Nat)(i : Fin n)(j : Fin n)
                  (p : Leq [n i j]) -> Leq [('suc n) ('fs n i) ('fs n j)]);

let trans {n : Nat}{i : Fin n}{j : Fin n}{k : Fin n}
          (p : Leq [n i j])(q : Leq [n j k]) : Leq [n i k];
refine trans n i j k p q <= Leq.Case [n i j] p;
refine trans ('suc n) ('fz n) j k ('leqz n j) q = 'leqz n k;
refine trans ('suc n) ('fs n i) ('fs n j) k ('leqs n i j p) q <= Leq.Case [('suc n) ('fs n j) k] q;