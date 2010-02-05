make NatD := con ['argf ['zero 'suc] [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

let add (x : Nat)(y : Nat) : Nat ;
lambda x, y ;
<= fold NatD x ;
induction Nat ;
    lambda y ;
    = y ;

    lambda y ;
    = suc ((Px y) call) ;

root;

let mul (x : Nat)(y : Nat) : Nat ;
lambda x, y ;
<= fold NatD x;
induction Nat ;
    lambda y ;
    = zero ;

    lambda y ;
    = add y ((Px y) call) ;

root;

elab mul two two