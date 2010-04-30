data List (A : Set) := (nil : List A) ; (cons : A -> List A -> List A) ;

let nil {A : Set} : List A ;
= List.nil A ;
root ;

let cons {A : Set}(a : A)(as : List A) : List A ;
= List.cons A a as ;
root ;

let sing {A : Set}(a : A) : List A ;
= cons a nil ;
root ;

let snoc (A : Set)(as : List A)(a : A) : List A ;
<= List.Ind A as ;
= sing a ;
next ;
= cons s^2 (snoc A xf^1 a) ;
root ;

let append (A : Set)(as : List A)(bs : List A) : List A ;
<= List.Ind A bs ;
= as ;
= append A (snoc A as s^2) xf^1 ;
root ;

make T := Enum ['a 'b 'c] : Set ;
make L := append T (cons 'a (cons 'b nil)) (sing 'c) : List T ;

let list-map (A : Set)(B : Set)(f : A -> B)(as : List A) : List B ;
<= [as] List.Ind A as ;
= nil ;
next ; 
= cons (f s^2) (list-map A B f xf^1) ;
root ;

elab list-map T (Enum ['x 'y]) ['x 'x 'y] L ;

data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= Nat.suc (plus xf^1 n) ;
root ;

let sum (xs : List Nat) : Nat ;
<= List.Ind Nat xs ;
= Nat.zero ;
= plus s^2 (sum xf^1) ;
root ;

make one := Nat.suc Nat.zero : Nat ;
make two := Nat.suc one : Nat ;
make three := Nat.suc two : Nat ;

elm sum (cons three (cons two (cons one (cons Nat.zero nil)))) ;