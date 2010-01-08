make Equiv :=
  (\ X R ->
  ((x : X) => R x x) &&
  (((x : X)(y : X) => R x y => R y x) &&
   ((x : X)(y : X)(z : X) => R x y => R y z => R x z)))
  : (X : *)(R : X -> X -> #) -> # ;

make Q := (\ X R p -> Quotient X R p)
       :  (X : *)(R : X -> X -> #)(p : :- Equiv X R) -> * ;

make cl := (\ X R p x -> [x])
        : (X : *)(R : X -> X -> #)(p : :- Equiv X R)(x : X) -> Q X R p ;

make ship := (\ X x y q P p ->
               coe(P x, P y, @ (([] : :- ((P : X -> *) == (P : X -> *)))
                                % x y []), p))
           : (X : *)(x : X)(y : X)(q : :- ((x : X) == (y : X)))(P : X -> *) -> P x -> P y ;

make thm : (X : *)(R : X -> X -> #)(p : :- Equiv X R) ->
           :- ((x : X)(y : X) => R x y => ([x] : Q X R p) == ([y] : Q X R p)) ;
lambda X ; lambda R ; lambda p ;
lambda x ; lambda y ; lambda eqxy ;
give @ ? ; lambda x2 ; lambda eqxx2 ;
give ship X x x2 eqxx2 (\ z -> :- R z y) eqxy

