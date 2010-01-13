make test := ? 
             : (A : *)
	       (B : A -> *)
	       (t : ( a : A ; B a)) -> A ;
in ;
lambda A ;
lambda B ;
lambda t ;
make e := split A B t 
          : (P : (a : A ; B a) -> *)
	    (f : (a : A)(b : B a) -> P [ a / b ]) -> P t ;
elim e ;
give \ a b -> a 