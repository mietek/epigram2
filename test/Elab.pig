make id := (\ X x -> x) : (X : Set) -> X -> X ;
make A := ? : Set ;
elm id _ A ;

make f := ? : ?a ;
elm f Set ;
jump f.a ;
give Set -> Set ;
root ;
elab elab ;