make NatD := con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := 'zero : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus : Nat -> Nat -> Nat ;
