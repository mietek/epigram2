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
make StreamD := (\ X -> con['sigmaD X \ x -> con['prodD 'tail (con ['idD]) (con['constD (Sig ())])]]) : Set -> Desc ;
make Stream := (\ X -> Nu (StreamD X)) : Set -> Set ;
make nats := (CoIt Nat (\ n -> [n (suc n)]) zero) : Stream Nat ;
make prune := (\ D -> con['sigmaD (Enum ['stop 'go]) [con['constD (Sig ())] D]]) : Desc -> Desc ;
make Prune := (\ D -> Mu (prune D)) : Desc -> Set ;
make prefix := (\ D -> con con [(con con \ n -> con['stop])
  (\ p -> con \ ih -> con \ t ->
     con['go , map D (Nu D) (Prune D) ih (t %)]) ] )
 : (D : Desc)(n : Nat) -> Nu D -> Mu (prune D) ;
make firstFour := prefix (StreamD Nat) four nats : Prune (StreamD Nat);
elab firstFour
