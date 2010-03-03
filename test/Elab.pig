make id := (\ X x -> x) : (X : Set) -> X -> X ;
make A := ? : Set ;
elm id _ A ;

make f := ? : ?a ;
elm f Set ;
jump f.a ;
give Set -> Set ;
root ;
elab elab ;

make x := ? : id _ Set ;

make B := _ : Set ;
make C := _ : Prop ;

make p := _ : :- (B == C) ;
make q := _ : :- (B == (: _) Set) ;

show state ;