make NatD := con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

let add (m : Nat)(n : Nat) : Nat ;
<= induction NatD m ;
= n ;
= suc (xf n call) ;

root;

let mul (m : Nat)(n : Nat) : Nat ;
<= induction NatD m;
= zero ;
= add n (xf n call) ;

root;

elab mul two two