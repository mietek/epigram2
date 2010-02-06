make NatD := con ['argf ['zero 'suc] [ (con ['done]) (con ['ind1 con ['done]]) ] ] : Desc ;
make Nat := (Mu NatD) : Set ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make zero := [] : Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
let plus (x : Nat)(y : Nat) : Nat ;
lambda x, y ;
elim inductionC NatD x ;
give [? ?] ;
     lambda r, y ;
     = y ;

     lambda h ;
     give con ? ;
     lambda ih ;
     give con ? ;
     lambda y ;
     = suc ((ih y) call) ;

root ;

elab plus two two