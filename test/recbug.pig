idata U : (:- TT) -> Set := ('pi : (S : Set) -> (T : S -> U _) -> U _);
let el (u : U _) : Set;
<= U.Ind _ u ;
= (s : S) -> el (T s)
