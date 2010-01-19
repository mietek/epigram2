make Nat := (Mu con ['arg (Enum ['zero 'suc]) [ (con ['done]) (con ['ind1 con ['done]]) ] ] ) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ r r y -> y) (\ r -> con \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;
make four := (plus two two) : Nat ;
make plusZ := con con [(con con []) (con \ x -> con con \ xh -> con [])] : (x : Nat) -> :- (plus x zero == x);
make ship := (\ X x y q P p ->
               coe(P x, P y, con (((: :- P == P) [])
                                % x y []), p))
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
make plzq := (con \ x y q ->
              ship Nat x y [] (\ y -> :- plus x zero == y)
              (plusZ x) %)
          : :- (((: Nat -> Nat) \ x -> plus x zero) == plus zero)
