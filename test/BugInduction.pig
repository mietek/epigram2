data Nat := ('zero : Nat) ; ('suc : Nat -> Nat) ;

let f (X : Set)(m : Nat)(Y : Set) : Nat ;
<= Nat.Ind m ;
root ;

let g (X : Set)(m : Nat)(Y : Set)(Z : Set) : Nat ;
<= Nat.Ind m ;
root ;

let h (W : Set)(X : Set)(m : Nat)(Y : Set) : Nat ;
<= Nat.Ind m ;
root ;

let f (X : Set)(x : X)(k : Nat) : Set ;
<= Nat.Ind k ;
root ;