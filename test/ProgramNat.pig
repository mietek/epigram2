make Nat := (Mu con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]]) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
root ;
make plus : Nat -> Nat -> Nat ;
program x, y ;
give con ? ;
give con ? ;
give [? ?] ;
lambda r ;
lambda r ;
lambda y ;
give return y ;
lambda r ;
give con ? ;
lambda h ;
lambda r ;
lambda y ;
give return (suc ((h y) call)) ;
root ;

make x := plus two two : Nat;
elab x
