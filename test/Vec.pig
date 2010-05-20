make Nat := (Mu con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD (con ['idD]) (con ['constD (Sig ())]) ])]]) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ _ _ y -> y) (\ _ -> con \ h _ y -> suc (h y))] : Nat -> Nat -> Nat ;
module Vec ;
lambda A : Set ;
make Vec : Nat -> Set ;
make VecD : Nat -> IDesc Nat ;
give (\ n -> IFSigma ['nil 'cons] [ (IConst (:- (n == zero))) (ISigma Nat (\
m -> IProd (IConst A) (IProd (IVar m) (IConst (:- (n == suc m)))))) ]) ;
lambda n ;
give IMu Nat VecD n ;
make nil := con ['nil , _] : Vec 'zero ;
make cons := (\ n a as -> con ['cons n a as , _]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ; 
make Vec : Nat -> Set ;
make VecD : Nat -> IDesc Nat ;
give (\ n -> IFSigma ['nil 'cons] [ (IConst (:- (n == ((: Nat) 'zero)))) (ISigma Nat (\ m -> IProd (IConst A) (IProd (IVar m) (IConst (:- (n == ((: Nat) ('suc m)))))))) ]) ;
lambda n ;
give IMu Nat VecD n ;
make nil := con ['nil , _] : Vec 'zero ;
make cons := (\ n a as -> con ['cons n a as , _]) : (n : Nat) -> A -> Vec n -> Vec (suc n) ;
root;  
