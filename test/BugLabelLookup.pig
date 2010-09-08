data List (A : Set) := ('nil : List A) ; ('cons : A -> List A -> List A) ;

let snoc (A : Set)(as : List A)(a : A) : List A ;
<= List.Ind A as ;
next ;
infer snoc ;