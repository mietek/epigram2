make ship := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
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
module Vec ;
lambda A : Set ;
make Vec : Nat -> Set ;
make VecD := (\ n -> IArg (Enum ['nil 'cons]) [ (IDone (zero == n)) (IArg Nat (\ m -> IArg A (\ a -> IInd1 m (IDone (suc m == n))))) ]) : Nat -> IDesc Nat ;
lambda n ;
give IMu Nat VecD n ;
make vnil := con [ 0 , _ ] : Vec zero ;
make vcons := (\ n a as -> con [ 1 n a as , _ ]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ;
make vappend := (\ m as -> iinduction Nat Vec.VecD m as (\ mas -> (n : Nat) -> Vec n -> Vec (plus (mas !) n)) (\ m -> con [ (\ p _ n as -> ship Nat zero m p (\ mm -> Vec (plus mm n)) as) (con \ mm -> con \ a -> con \ as p -> con \ appp _ n as -> ship Nat (con ['suc mm]) m p (\ mmm -> Vec (plus  mmm n)) (vcons (plus mm n) a (appp n as))) ])) : (m : Nat) -> Vec m -> (n : Nat) -> Vec n -> Vec (plus m n) ;
root ;
make ex := Vec.vcons Nat one zero (Vec.vcons Nat zero one (Vec.vnil Nat)) : Vec.Vec Nat two ;
elab ex