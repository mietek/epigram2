data Nat := ('zero : Nat) ; ('suc : Nat -> Nat);
data List (X : Set) := ('nil : List X) ; ('cons : X -> List X -> List X);
data Tree (X : Set) := ('leaf : Tree X) ; ('node : X -> Tree X -> Tree X -> Tree X);