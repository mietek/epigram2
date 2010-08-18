-- Inspired by opSimp (written by Ulf)

--
-- map id x = x:
--

let id {A : Set}(a : A) : A ;
= a ;
root ;

let law-map-id (D : Desc)(X : Set)(x : desc D X) : Set ;
= :- map D X X id x == x ;
root ;

let simpl-map-id (D : Desc)(X : Set)(x : desc D X) : law-map-id D X x ;
-- MAGIC!
root ;


-- 
-- map swap (map swap x) = x
--

let swap {A : Set}{B : Set}(x : Sig (A ; B ;)) : Sig (B ; A ;) ;
define swap A B [a b] := [b a] ;
root ;

let law-map-ss (D : Desc)(A : Set)(B : Set)(x : desc D (Sig (A ; B ;))) : Set ;
= (:- (map D (Sig (B ; A ;)) (Sig (A ; B ;)) (swap./ B A)
          (map D (Sig (A ; B ;)) (Sig (B ; A ;)) (swap./ A B) x)) ==
           x) ;
root ;

let simpl-map-ss (D : Desc)(A : Set)(B : Set)(x : desc D (Sig (A ; B ;)))
                 : law-map-ss D A B x ;
-- MAGIC!
root;