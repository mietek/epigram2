data Nat := ('zero : Nat) ; ('suc : Nat -> Nat) ;

let A (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
define A 'zero n := 'suc n ;
<= Nat.Ind n ;
define A ('suc m) 'zero := A m ('suc 'zero) ;
define A ('suc m) ('suc n) := A m (A ('suc m) n) ;
give \ n -> _ ;
root ;

elab A 'zero 'zero ;
elab A ('suc 'zero) 'zero ;
elab A ('suc ('suc 'zero)) 'zero ;
elab A ('suc ('suc ('suc 'zero))) 'zero ;
elab A ('suc ('suc ('suc ('suc 'zero)))) 'zero ;
elab A 'zero ('suc 'zero) ;
elab A ('suc 'zero) ('suc 'zero) ;
elab A ('suc ('suc 'zero)) ('suc 'zero) ;
elab A ('suc ('suc ('suc 'zero))) ('suc 'zero) ;
elab A 'zero ('suc ('suc 'zero)) ;
elab A ('suc 'zero) ('suc('suc 'zero)) ;
elab A ('suc ('suc 'zero)) ('suc('suc 'zero)) ;
elab A ('suc ('suc ('suc 'zero))) ('suc('suc 'zero)) ;