make Nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := [] : Nat ;
make suc := (\ x -> [x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
module Vec ;
lambda A : * ;
make Vec : Nat -> * ;
make VecD := (\ n -> IArg { nil , cons } [ (IDone ((n : Nat) == (zero : Nat))) (IArg Nat (\ m -> IArg A (\ a -> IInd1 m (IDone ((n : Nat) == (suc m : Nat)))))) ]) : Nat -> IDesc Nat ;
lambda n ;
give IMu Nat VecD n ;
make vnil := @ [ 0 / [] ] : Vec zero ;
make vcons := (\ n a as -> @ [ 1 n a as / [] ]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ;
root ;
make ex := Vec.vcons Nat one zero (Vec.vcons Nat zero one (Vec.vnil Nat)) : Vec.Vec Nat two ; 
module BVec  ;
lambda A : * ;
make Vec : Nat -> * ;
make VecD : Nat -> IDesc Nat ;
give @ @ [ (@ @ (IDone TT)) (@ (\ m -> @ (\ h -> IArg A (\ a -> IInd1 m (IDone TT))))) ] ;
lambda n ;
give IMu Nat VecD n ;
make vnil := @ [] : Vec zero ;
make vcons := (\ n a as -> @ [ a as / [] ]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ;
root ;
make ex2 := BVec.vcons Nat one zero (BVec.vcons Nat zero one (BVec.vnil Nat)) : BVec.Vec Nat two  


