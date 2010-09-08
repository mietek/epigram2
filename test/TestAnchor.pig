data List (A : Set) := ('nil : List A) ; ('cons : A -> List A -> List A) ;
elab List;

data List2 (A : Set)(B : Set) := ('nil : List2 A B) ; ('cons : A -> B -> List2 A B -> List2 A B) ;
elab List2;
