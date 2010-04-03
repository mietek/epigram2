make ship := (\ X x y q P p ->
coe (P x) (P y) (con (((: :- ((: X -> Set) P == (: X -> Set) P)) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- (x == y))(P : X -> Set) -> P x -> P y ;

make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : Set)(R : X -> X -> Prop) -> Prop ;

make eqQ : (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R) ->
           :- ((x : X)(y : X) => R x y => (: Quotient X R p) [x] == (: Quotient X R p) [y]) ;
lambda X ; lambda R ; lambda p ;
lambda x ; lambda y ; lambda eqxy ;
give con ? ; lambda x2 ; lambda eqxx2 ;
give ship X x x2 eqxx2 (\ z -> :- R z y) eqxy ; root ;

make Plus := (\ A B ->
  Mu con ['sigmaD (Enum ['inl 'inr])
          [ con ['sigmaD A (\ x -> con ['constD (Sig ())])]
            con ['sigmaD B (\ y -> con ['constD (Sig ())])]
          ]
       ]
  ) :  Set -> Set -> Set ;

make inl := (\ A B x -> con ['inl x] ) : (A : Set)(B : Set)(x : A) -> Plus A B ;
make inr := (\ A B y -> con ['inr y] ) : (A : Set)(B : Set)(y : B) -> Plus A B ;

make Or := (\ A B -> Inh (Plus (:- A) (:- B))) : Prop -> Prop -> Prop ;

make EqUPair
  := (\ A p q -> Or ((p !) == (q !) && (p -) == (q -))
                    ((p !) == (q -) && (p -) == (q !)))
  : (A : Set) -> Sig (A ; A) -> Sig (A ; A) -> Prop ;

module UnorderedPair ;
lambda A : Set ; 
lambda isEquiv : :- Equiv (Sig (A ; A)) (EqUPair A) ; 

make UPair := Quotient (Sig (A ; A)) (EqUPair A) isEquiv : Set ;

make upair := (\ x y -> [[x , y]]) : A -> A -> UPair ;

make upairSym := (\ x y -> ?) 
  : (x : A)(y : A) -> :- (upair x y) == (upair y x) ;
next ;
give eqQ (Sig (A ; A)) (EqUPair A) isEquiv [x , y] [y , x] (wit con ['inr _]) 
 
