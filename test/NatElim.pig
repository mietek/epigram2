make NatD := con ['arg (Enum ['zero 'suc]) [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make add : Nat -> Nat -> Nat ;
lambda x ;
lambda y ;
elim elimOp NatD x ;
    give con ? ;
    lambda x ;
    elim Switch ['zero 'suc] x ;

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
