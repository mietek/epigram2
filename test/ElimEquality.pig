make X := ? : Set ;
make x := ? : X ;
make t := ? : X ;
make e := ? : (P : X -> Set) -> P t -> P x ;
make T := ? : X -> Set ;
make a : T x ;
elim e ;