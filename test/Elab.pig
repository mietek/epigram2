make id := (\ X x -> x) : (X : Set) -> X -> X ;
make A := ? : Set ;
elm id _ A ;
elab elab ;

make f := ? : ?a ;
elm f Set ;
elab elab ;
jump f.a ;
give Set -> Set ;
out ;
cdown ;
elab elab ;