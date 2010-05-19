make X := ? : Set ;
make Y := ? : X -> Set ;
make Z := ? : Set ;
make f : Sig X Y -> Z ;
lambda xy ;
elim split X Y xy ;
root ;
show state ;