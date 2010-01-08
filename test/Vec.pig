make Nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := [] : Nat ;
make suc := (\ x -> [x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make Dummy : * -> () ;
lambda A ;
make Vec : Nat -> * ;
make VecD := (\ n -> IArg { nil , cons } [ (IDone ((n : Nat) == (zero : Nat))) (IArg Nat (\ m -> IArg A (\ a -> IInd1 m (IDone ((n : Nat) == (suc m : Nat)))))) ]) : Nat -> IDesc Nat ;
lambda n ;
give IMu Nat VecD n ;
make vnil := @ [ 0 / [] ] : Vec zero ;
make vcons := (\ n a as -> @ [ 1 n a as / [] ]) : (n : Nat) -> A -> Vec n -> Vec (suc n)

