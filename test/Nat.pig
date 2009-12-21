make nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := [] : nat ;
make suc := (\ x -> [x]) : nat -> nat ;
make one := (suc zero) : nat ;
make two := (suc one) : nat ;
make plus := @ @ [(\ r r y -> y) (\ r -> @ \ h r y -> suc (h y))] : nat -> nat -> nat ;
make x := (plus two two) : nat