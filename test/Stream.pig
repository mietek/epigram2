make Nat := (Mu con ['arg (Enum ['zero 'suc]) [ (con ['done]) (con ['ind1 con ['done]]) ] ] ) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := con con [(\ r r y -> y) (\ r -> con \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;
make four := (plus two two) : Nat ;
make StreamD := (\ X -> con['arg X \ x -> con['ind1 con['done]]]) : Set -> Desc ;
make Stream := (\ X -> Nu (StreamD X)) : Set -> Set ;
make nats := (CoIt Nat (\ n -> [n (suc n)]) zero) : Stream Nat ;
make prune := (\ D -> con['arg (Enum ['stop 'go]) [con['done] D]]) : Desc -> Desc ;
make Prune := (\ D -> Mu (prune D)) : Desc -> Set ;
make prefix := (\ D -> con con [(con con \ n -> con['stop])
  (\ p -> con \ ih -> con \ t ->
     con['go , map(D, Nu D, Prune D, ih, t %)]) ] )
 : (D : Desc)(n : Nat) -> Nu D -> Mu (prune D) ;
make firstFour := prefix (StreamD Nat) four nats : Prune (StreamD Nat)


