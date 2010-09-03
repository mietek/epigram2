make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;

make Bool := (Enum ['true 'false]) : Set ;

make SoD : Bool -> IDesc Bool;
lambda b ;
give 'fsigmaD ['oh] [('constD (:- ((: Bool) 'true) == b))] ;

make So : Bool -> Set ;
lambda b ;
give IMu Bool SoD b ;

make oh := 'oh : So 'true ;

make foo := (\ b p -> ship Bool 'true b p So 'oh) : (b : Bool) -> (:- ((: Bool) 'true == b)) -> So b ;

make no : So 'false -> :- FF ;
lambda x ;
<= iinduction Bool SoD 'false x ;
root ;
