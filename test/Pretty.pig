make f := (\ x -> ?) : * -> * -> * ;
make g := (\ x y -> ?) : * -> * -> * ;
make h := ? : * -> * -> * ;
make h2 := ? : (* -> *) -> * ;
make h3 := ? : * -> (* -> *) -> * ;
make h4 := ? : (* -> * -> *) -> * ;
make h5 := ? : (* -> *) -> * -> * ;
make h6 := ? : ((* -> *) -> *) -> * ;

make A := {a, b} : * ;

make a := ? : * ;
make P := a == a : # ;
make G := ? : :- P ;

make k := ? : (x : *)(y : *) -> :- x == y -> * ;

elab A ;
show context ;

make nat : Desc ;
give @ ? ;