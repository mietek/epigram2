make ship := (\ X x y q P p ->
               coe(P x, P y, con (([] : :- ((P : X -> Set) == (P : X -> Set)))
                                % x y []), p))
           : (X : Set)(x : X)(y : X)(q : :- ((x : X) == (y : X)))(P : X -> Set) -> P x -> P y ;

make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : Set)(R : X -> X -> Prop) -> Prop ;

make eqQ : (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R) ->
           :- ((x : X)(y : X) => R x y => ([x] : Quotient X R p) == ([y] : Quotient X R p)) ;
lambda X ; lambda R ; lambda p ;
lambda x ; lambda y ; lambda eqxy ;
give con ? ; lambda x2 ; lambda eqxx2 ;
give ship X x x2 eqxx2 (\ z -> :- R z y) eqxy ; root ;

make Plus := (\ A B ->
  Mu con ['arg (Enum ['inl 'inr])
          [ con ['arg A (\ x -> con ['done])]
            con ['arg B (\ y -> con ['done])]
          ]
       ]
  ) :  Set -> Set -> Set ;

make inl := (\ A B x -> con ['inl x] ) : (A : Set)(B : Set)(x : A) -> Plus A B ;
make inr := (\ A B y -> con ['inr y] ) : (A : Set)(B : Set)(y : B) -> Plus A B ;

make Or := (\ A B -> Inh (Plus (:- A) (:- B))) : Prop -> Prop -> Prop ;

make EqUPair
  := (\ A p q -> Or ((p ! : A) == (q ! : A) && (p - : A) == (q - : A))
                    ((p ! : A) == (q - : A) && (p - : A) == (q ! : A)))
  : (A : Set) -> Sig (A ; A) -> Sig (A ; A) -> Prop ;

module UnorderedPair ;
lambda A : Set ; 
lambda isEquiv : :- Equiv (Sig (A ; A)) (EqUPair A) ; 

make UPair := Quotient (Sig (A ; A)) (EqUPair A) isEquiv : Set ;

make upair := (\ x y -> [[x , y]]) : A -> A -> UPair ;

make upairSym := (\ x y -> ?) 
  : (x : A)(y : A) -> :- (upair x y : UPair) == (upair y x : UPair) ;
next ;
give eqQ (Sig (A ; A)) (EqUPair A) isEquiv [x , y] [y , x] (wit con ['inr []]) 
 
