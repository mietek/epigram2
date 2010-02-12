make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
make Bool := (Enum ['true 'false]) : Set ;
make So : Bool -> Set ;
lambda b ;
give IMu Bool (\ b -> IDone (((: Bool) 'true) == b)) b ;
make oh := con _ : So 'true ;
make foo := (\ b p -> ship Bool 'true b p So oh) : (b : Bool) -> (:- ((: Bool) 'true == b)) -> So b 
