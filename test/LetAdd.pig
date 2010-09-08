make NatD := con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := 'zero : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

let add (m : Nat)(n : Nat) : Nat ;
<= induction NatD m ;
= n ;
= suc (nh n call) ;

root;
elab add two two ;
