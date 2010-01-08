make ship := (\ X x y q P p ->
               coe(P x, P y, @ (([] : :- ((P : X -> *) == (P : X -> *)))
                                % x y []), p))
           : (X : *)(x : X)(y : X)(q : :- ((x : X) == (y : X)))(P : X -> *) -> P x -> P y ;

make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : *)(R : X -> X -> #) -> # ;

make eqQ : (X : *)(R : X -> X -> #)(p : :- Equiv X R) ->
           :- ((x : X)(y : X) => R x y => ([x] : Quotient X R p) == ([y] : Quotient X R p)) ;
lambda X ; lambda R ; lambda p ;
lambda x ; lambda y ; lambda eqxy ;
give @ ? ; lambda x2 ; lambda eqxx2 ;
give ship X x x2 eqxx2 (\ z -> :- R z y) eqxy ; root ;

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

make Module : (A : *)(isEquiv : :- Equiv (A ; A) (EqUPair A)) -> * ;
lambda A ; lambda isEquiv ;

make UPair := Quotient (A ; A) (EqUPair A) isEquiv
           :  * ;

make upair := (\ x y -> [[x / y]]) : A -> A -> UPair ;

make upairSym := (\ x y -> ?)
  : (x : A)(y : A) ->
    :- (upair x y : UPair) == (upair y x : UPair) ;
  next ;
  give eqQ (A ; A) (EqUPair A) isEquiv [x / y] [y / x] (wit @ [`inr []])
  
