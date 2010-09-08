make Nat := (Mu con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]]) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ r r y -> y) (\ r -> con \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;
make four := (plus two two) : Nat ;
make plusZ := con con [(con con _) (con \ x -> con con \ xh -> con _)] : (x : Nat) -> :- (plus x zero == x);
make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _))  p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
make plzq := (con \ x y q ->
              ship Nat x y _ (\ y -> :- plus x zero == y)
              (plusZ x) %)
          : :- (((: Nat -> Nat) \ x -> plus x zero) == plus zero)
