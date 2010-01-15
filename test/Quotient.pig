make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : Set)(R : X -> X -> Prop) -> Prop ;

make Q := (\ X R p -> Quotient X R p)
       :  (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R) -> Set ;

make cl := (\ X R p x -> [x])
        : (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R)(x : X) -> Q X R p ;

make ship := (\ X x y q P p ->
               coe(P x, P y, con (([] : :- ((P : X -> Set) == (P : X -> Set)))
                                % x y []), p))
           : (X : Set)(x : X)(y : X)(q : :- ((x : X) == (y : X)))(P : X -> Set) -> P x -> P y ;

make thm : (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R) ->
           :- ((x : X)(y : X) => R x y => ([x] : Q X R p) == ([y] : Q X R p)) ;
lambda X ; lambda R ; lambda p ;
lambda x ; lambda y ; lambda eqxy ;
give con ? ; lambda x2 ; lambda eqxx2 ;
give ship X x x2 eqxx2 (\ z -> :- R z y) eqxy ; root ;

make qel : (X : Set)(R : X -> X -> Prop)(p : :- Equiv X R)
           (z : Q X R p)(P : Q X R p -> Set)
           (m : (x : X) -> P [x]) ->
           :- ((x : X)(y : X) => R x y => (m x : P [x]) == (m y : P [y])) ->
           P z ;
give (\ X R p z P m h -> qElim(X, R, p, z, P, m, h)) ; root

