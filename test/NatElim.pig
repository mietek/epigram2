make NatD := con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := 'zero : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make add : Nat -> Nat -> Nat ;
lambda x ;
lambda y ;
elim induction NatD x ;
    give con ? ;
    lambda x ;
    elim switch ['zero 'suc] x ;
    give [? ?] ;

	lambda m  ;
        lambda n ;
        give con ? ;
        give con ? ;
        lambda y ;
        give y ; 

        lambda m ;
        lambda n ;
        lambda k ;
        give con ? ;
        lambda ih ;
        give con ? ; 
        lambda y ; 
        give suc (ih y) ;

root ;
elab add two two ;
