make Nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := [] : Nat ;
make suc := (\ x -> [x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := @ @ [(\ r r y -> y) (\ r -> @ \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;
make four := (plus two two) : Nat ;
make plusZ := @ @ [(@ @ []) (@ \ x -> @ @ \ xh -> @ [])] : (x : Nat) -> :- (plus x zero == x);
make ship := (\ X x y q P p ->
               coe(P x, P y, @ (([] : :- ((P : X -> *) == (P : X -> *)))
                                % x y []), p))
           : (X : *)(x : X)(y : X)(q : :- x == y)(P : X -> *) -> P x -> P y ;
make plzq := (@ \ x y q ->
              ship Nat x y [] (\ y -> :- (plus x zero == y)  )
              (plusZ x) %)
          : :- ((\ x -> plus x zero) : Nat -> Nat) == plus zero
