make Nat : Set ;
make NatD := con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD (con ['idD]) (con ['constD (Sig ())]) ])]] : Desc ;
give Mu NatD ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make N-case := (\ n P m0 ms -> induction Nat.NatD n P (con [ (con con m0) (con \ k -> con \ _ -> ms k) ] )) 
                : (n : Nat)(P : Nat -> Set) -> 
                   P [] -> 
                   ((k : Nat) -> P (con ['suc k])) ->
                   P n ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ _ _ y -> y) (\ _ -> con \ h _ y -> suc (h y))] : Nat -> Nat -> Nat ;
module Vec  ;
lambda A : Set ;
make Vec : Nat -> Set ;
make VecD : Nat -> IDesc Nat ;
lambda n ;
elim N-case n ;
give \ _ -> IDone TT ;
give \ m _ -> IArg A (\ a -> IInd1 m (IDone TT)) ;
prev ;
lambda n ;
give IMu Nat VecD n ;
make vnil := con _ : Vec zero ;
make vcons := (\ n a as -> con [ a as , _ ]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ;
root ;
make bvappend : (A : Set) -> (m : Nat) -> Vec.Vec A m -> (n : Nat) -> Vec.Vec A n -> Vec.Vec A (plus m n) ;
lambda A ;
give (\ m as -> iinduction Nat (Vec.Vec.VecD A) m as (\ mas -> (n : Nat) -> Vec.Vec A n -> Vec.Vec A (plus (mas !) n)) ?) ;
lambda m ;
elim N-case m ;
give \ _ _ _ _ _ n bs -> bs ;
give \ k A _ _ -> con \ a as -> con \ appp _ n bs -> Vec.vcons A (plus k n) a (appp n bs) ;
root ;
make ex := Vec.vcons Nat one zero (Vec.vcons Nat zero one (Vec.vnil Nat)) : Vec.Vec Nat two