make NatD := con ['argf ['zero 'suc] [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make add := ? : Nat -> Nat -> Nat ;
make add : (x : Nat) -> (y : Nat) -> < add x y : Nat > ;
lambda x ;
lambda y ;
elim fold NatD x ;
induction Nat ;
    lambda y;
    give return y;

    lambda y;
    give return (suc ((Px y) call));

root;

elab add two two;