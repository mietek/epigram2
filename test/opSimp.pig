make swap :=
  (\ A B -> con (\ x -> con (\ y -> con [ y x ]))) :
  (A : Set)(B : Set) -> Sig (A ; B ;) -> Sig (B ; A ;) ;

make id := (\ A x -> x) : (A : Set) -> A -> A ;

make law1 :=
  (\ D A x -> :- (map(D, A, A, id A, x) : descOp(D, A)) == (x : descOp(D, A))
  ) :
  (D : Desc)(A : Set)(x : descOp(D, A)) -> Set ;

make lawswap :=
  (\ D A B x ->
      :- (map(D, Sig (B ; A ;), Sig (A ; B ;), swap B A,
          map(D, Sig (A ; B ;), Sig (B ; A ;), swap A B, x)) : descOp(D, Sig (A ; B ;))) ==
         (x : descOp(D, Sig (A ; B ;)))
  ) :
  (D : Desc)(A : Set)(B : Set)(x : descOp(D, Sig (A ; B ;))) -> Set ;

make prf1 := (\ D A x -> []) : (D : Desc)(A : Set)(x : descOp(D, A)) -> law1 D A x ;

make prfswap : (D : Desc)(A : Set)(B : Set)(x : descOp(D, Sig (A ; B ;))) -> lawswap D A B x ;
give (\ D A B x -> []) ;

make monad1 :=
  (\ D X t -> :- (subst(D, X, X, (\ x -> ` x), t) : Monad D X) ==
                 (t : Monad D X)) :
  (D : Desc)(X : Set)(t : Monad D X) -> Set ;

make prfmonad1 := (\ D X t -> []) :
      (D : Desc)(X : Set)(t : Monad D X) -> monad1 D X t ;

make monad3 :=
  (\ D X Y Z f g t -> :-
    (subst(D, Y, Z, f, subst(D, X, Y, g, t)) : Monad D Z) ==
    (subst(D, X, Z, (\ x -> subst(D, Y, Z, f, g x)), t) : Monad D Z)
  ) :
  (D : Desc)(X : Set)(Y : Set)(Z : Set)
  (f : Y -> Monad D Z)(g : X -> Monad D Y)(t : Monad D X) -> Set ;

make monad3prf :=
  (\ D X Y Z f g t -> []) :
  (D : Desc)(X : Set)(Y : Set)(Z : Set)
  (f : Y -> Monad D Z)(g : X -> Monad D Y)(t : Monad D X) -> monad3 D X Y Z f g t

