make swap :=
  (\ A B -> @ (\ x -> @ (\ y -> @ [ y x ]))) :
  (A : *)(B : *) -> (A ; B ;) -> (B ; A ;) ;

make id := (\ A x -> x) : (A : *) -> A -> A ;

make law1 :=
  (\ D A x -> :- (map(D, A, A, id A, x) : descOp(D, A)) == (x : descOp(D, A))
  ) :
  (D : Desc)(A : *)(x : descOp(D, A)) -> * ;

make lawswap :=
  (\ D A B x ->
      :- (map(D, (B ; A ;), (A ; B ;), swap B A,
          map(D, (A ; B ;), (B ; A ;), swap A B, x)) : descOp(D, (A ; B ;))) ==
         (x : descOp(D, (A ; B ;)))
  ) :
  (D : Desc)(A : *)(B : *)(x : descOp(D, (A ; B ;))) -> * ;

make prf1 := (\ D A x -> []) : (D : Desc)(A : *)(x : descOp(D, A)) -> law1 D A x ;

make prfswap : (D : Desc)(A : *)(B : *)(x : descOp(D, (A ; B ;))) -> lawswap D A B x ;
give (\ D A B x -> [])

