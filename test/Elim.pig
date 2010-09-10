make test := ? 
             : (A : Set)
	       (B : A -> Set)
	       (t : Sig (a : A ; B a)) -> A ;
in ;
lambda A ;
lambda B ;
lambda t ;
make e := split A B t 
          : (P : Sig (a : A ; B a) -> Set)
	    (f : (a : A)(b : B a) -> P [ a , b ]) -> P t ;
elim e ;
give \ A B a b -> a 