make NatD := con ['argf ['zero 'suc] [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

let add (x : Nat)(y : Nat) : Nat ;
<= induction NatD x ;
= delta ;
= suc (x delta call) ;

root;

let mul (x : Nat)(y : Nat) : Nat ;
<= induction NatD x;
= zero ;
= add y (x delta call) ;

root;

elab mul two two