make nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := @ [`zero] : nat ;
make suc := (\ x -> @ [`suc x]) : nat -> nat ;
make one := (suc zero) : nat ;
make two := (suc one) : nat ;
root ;
make plus : nat -> nat -> nat ;
program x, y ;
give @ ? ;
give @ ? ;
give [? ?] ;
lambda r ;
lambda r ;
lambda y ;
give return y ;
lambda r ;
give @ ? ;
lambda h ;
lambda r ;
lambda y ;
give return (suc ((h y) call)) ;
root ;

make x := plus two two : nat
