data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;

-- Okay, so this is cheating: we implement the Ackermann function
-- using higher-order magic.

let Iter (f : Nat -> Nat)(n : Nat) : Nat ;
<= Nat.Ind n ;
= f ('suc 'zero) ;
= f (Iter f n) ;
root ;

let A (m : Nat) : Nat -> Nat ;
<= Nat.Ind m ;
= Nat.suc ;
= Iter (A n) ;
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
