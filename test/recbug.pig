idata U : (:- TT) -> Set := (pi : (S : Set) -> (S -> U _) -> U _);
let el (u : U _) : Set;
<= U.Ind _ u ;
= (x : s) -> el (xf^1 x)
