make NatDesc := con ['sumD ['zero 'suc]
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
make Nat := (Mu NatDesc) : Set ;

make plus : Nat -> Nat -> Nat ;
lambda m, n ;
elim induction NatDesc m ;
