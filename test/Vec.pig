make Nat := (Mu con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]]) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ _ _ y -> y) (\ _ -> con \ h _ y -> suc (h y))] : Nat -> Nat -> Nat ;
module Vec ;
lambda A : Set ;
make Vec : Nat -> Set ;
make VecD : Nat -> IDesc Nat ;
give (\ n -> 'fsigmaD ['nil 'cons] [ ('constD (:- (n == zero))) ('sigmaD Nat (\ m -> 'prodD 'a ('constD A) ('prodD 'as ('varD m) ('constD (:- (n == suc m)))))) ]) ;
lambda n ;
give IMu Nat VecD n ;
make nil := 'nil : Vec 'zero ;
make cons := (\ n a as -> 'cons n a as) : (n : Nat) -> A -> Vec n -> Vec (suc n) ; 
