data List (A : Set) := ('nil : List A) ; ('cons : A -> List A -> List A) ;

let nil {A : Set} : List A ;
define nil _ := 'nil ;
root ;

let cons {A : Set}(a : A)(as : List A) : List A ;
define cons _ a as := 'cons a as ;
root ;

let sing {A : Set}(a : A) : List A ;
define sing _ a := cons a nil ;
root ;

let snoc (A : Set)(as : List A)(a : A) : List A ;
<= List.Ind A as ;
define snoc _ 'nil a := sing a ;
define snoc A ('cons x xs) a := cons x (snoc A xs a) ;
root ;

let append (A : Set)(as : List A)(bs : List A) : List A ;
<= List.Ind A bs ;
define append _ as 'nil := as ;
define append A as ('cons b bs) := append A (snoc A as b) bs ;
root ;

make T := Enum ['a 'b 'c] : Set ;
make L := append T (cons 'a (cons 'b nil)) (sing 'c) : List T ;

let list-map (A : Set)(B : Set)(f : A -> B)(as : List A) : List B ;
<= List.Ind A as ;
define list-map _ _ _ 'nil := 'nil ;
define list-map A B f ('cons a as) := 'cons (f a) (list-map A B f as) ;
root ;

elab list-map T (Enum ['x 'y]) ['x 'x 'y] L ;

data Nat := ('zero : Nat) ; ('suc : Nat -> Nat) ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
define plus 'zero n := n ;
define plus ('suc m) n := 'suc (plus m n) ;
root ;

let sum (xs : List Nat) : Nat ;
<= List.Ind Nat xs ;
define sum 'nil := Nat.zero ;
define sum ('cons x xs) := plus x (sum xs) ;
root ;

make one := Nat.suc Nat.zero : Nat ;
make two := Nat.suc one : Nat ;
make three := Nat.suc two : Nat ;

elm sum (cons three (cons two (cons one (cons Nat.zero nil)))) ;