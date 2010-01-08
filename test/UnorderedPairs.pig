make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : *)(R : X -> X -> #) -> # ;

make Plus := (\ A B ->
  Mu @ [`arg {inl, inr}
          [ @ [`arg A (\ x -> @ [`done])]
            @ [`arg B (\ y -> @ [`done])]
          ]
       ]
  ) :  * -> * -> * ;

make inl := (\ A B x -> @ [`inl x] ) : (A : *)(B : *)(x : A) -> Plus A B ;
make inr := (\ A B y -> @ [`inr y] ) : (A : *)(B : *)(y : B) -> Plus A B ;

make Or := (\ A B -> Inh (Plus (:- A) (:- B))) : # -> # -> # ;

make EqUPair
  := (\ A p q -> Or ((p ! : A) == (q ! : A) && (p - : A) == (q - : A))
                    ((p ! : A) == (q - : A) && (p - : A) == (q ! : A)))
  : (A : *) -> (A ; A) -> (A ; A) -> # ;

make isEquiv
  := (\ A -> ?)
  :  (A : *) -> :- Equiv (A ; A) (EqUPair A) ;
  next ;
  give [ ? ? ] ;
    give (\ p -> wit @ [`inl []]) ;
    give (\ p q eqpq -> ?) ;
  root ;

make UPair := (\ A -> Quotient (A ; A) (EqUPair A) (isEquiv A))
           :  * -> *

