data Nat := (zero : Nat) ; (suc : (n : Nat) -> Nat);

let Le (x : Nat)(y : Nat) : Prop;
<= Nat.Ind x;
define Le 'zero y := TT;
<= Nat.Ind y;
define Le ('suc x) 'zero := FF;
define Le ('suc x) ('suc y) := Le x y;
root;

{-
let owotoNat (x : Nat)(y : Nat)(P : Nat -> Nat -> Set)
             (ple : (x : Nat)(y : Nat) -> (:- Le x y) -> P x y)
             (pge : (x : Nat)(y : Nat) -> (:- Le y x) -> P x y)
             : P x y
-}
let owotoNat (x : Nat)(y : Nat)(P : Nat -> Nat -> Set)             (ple : (x : Nat)(y : Nat) -> (:- Le x y) -> P x y)             (pge : (x : Nat)(y : Nat) -> (:- Le y x) -> P x y)             : P x y;
<= Nat.Ind x;
define owotoNat 'zero y P ple pge := ple 'zero y _;
<= Nat.Ind y;
define owotoNat ('suc x) 'zero P ple pge := pge ('suc x) 'zero _;
relabel owotoNat ('suc x) ('suc y) P ple pge;
<= owotoNat x y;
define owotoNat ('suc x) ('suc y) P ple pge := ple ('suc x) ('suc y) _;
  give xf;
