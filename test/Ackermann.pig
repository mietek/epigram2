data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

-- Okay, so this is cheating: we implement the Ackermann function
-- using higher-order magic.

let Iter (f : Nat -> Nat)(n : Nat) : Nat ;
<= [n] Nat.Ind n ;
= f ('suc 'zero) ;
= f (Iter f xf^1) ;
root ;

let A (m : Nat) : Nat -> Nat ;
<= Nat.Ind m ;
= Nat.suc ;
= Iter (A xf^1) ;
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