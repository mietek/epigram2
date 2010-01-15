make f := (\ x -> ?) : Set -> Set ;
make g := (\ x y -> ?) : Set -> Set -> Set ;
make h := ? : Set -> Set -> Set ;
make h2 := ? : (Set -> Set) -> Set ;
make h3 := ? : Set -> (Set -> Set) -> Set ;
make h4 := ? : (Set -> Set -> Set) -> Set ;
make h5 := ? : (Set -> Set) -> Set -> Set ;
make h6 := ? : ((Set -> Set) -> Set) -> Set ;

make A := (Enum ['a 'b]) : Set ;

make a := ? : Set ;
make P := a == a : Prop ;
make G := ? : :- P ;

make k := ? : (x : Set)(y : Set) -> :- x == y -> Set ;

make B := Sig (x : Set ; x -> Set) : Set ;
make y := [Set , f] : B ;

make C := Sig (x : Set ; Set ; Set ;) : Set ;
make z := [Set Set Set] : C ;

show context ;
elab A ;
elab B ;
elab f B ;
elab y ;
elab z ;
