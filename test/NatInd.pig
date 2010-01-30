make NatD := con ['argf ['zero 'suc] [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make ind : (n : Nat)(P : Nat -> Set) -> P zero -> ((k : Nat) -> P k -> P (suc k)) -> P n;
lambda n ;
elim fold NatD n ;
    give con ? ;
    lambda x ;
    elim switch ['zero 'suc] x ;
    give [? ?] ;
        lambda n ;
	give con ? ;
	give con ? ;
	lambda P ;
	lambda bc ;
	lambda ih ;
	give bc ;

	lambda n ;
	give con ? ;
	lambda r ; 
	give con ? ;
	give con ? ;
	lambda iih ;
	give con ? ;
	lambda P ;
	lambda bc ;
	lambda ih ;
	give ih r (iih P bc ih) ;

root ;

