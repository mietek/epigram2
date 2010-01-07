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
give (\ D A B x -> []) ;

make monad1 :=
  (\ D X t -> :- (subst(D, X, X, (\ x -> ' x), t) : Monad D X) ==
                 (t : Monad D X)) :
  (D : Desc)(X : *)(t : Monad D X) -> * ;

make prfmonad1 := (\ D X t -> []) :
      (D : Desc)(X : *)(t : Monad D X) -> monad1 D X t ;

make monad3 :=
  (\ D X Y Z f g t -> :-
    (subst(D, Y, Z, f, subst(D, X, Y, g, t)) : Monad D Z) ==
    (subst(D, X, Z, (\ x -> subst(D, Y, Z, f, g x)), t) : Monad D Z)
  ) :
  (D : Desc)(X : *)(Y : *)(Z : *)
  (f : Y -> Monad D Z)(g : X -> Monad D Y)(t : Monad D X) -> * ;

make monad3prf :=
  (\ D X Y Z f g t -> []) :
  (D : Desc)(X : *)(Y : *)(Z : *)
  (f : Y -> Monad D Z)(g : X -> Monad D Y)(t : Monad D X) -> monad3 D X Y Z f g t

