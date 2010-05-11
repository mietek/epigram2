make D := ? : Desc ;
make X := ? : Set ;
let f : desc D X ;
root ;

make e := ? : EnumU ;
make p := ? : Enum e -> Set ;
let g : branches e p ;
root ;

make A := ? : Set ;
make B := ? : A -> Set ;
make ab := ? : Sig A B ;
make p := ? : (a : A)(b : B a) -> Set ;
let h : split A B ab (\ _ -> Set) p ;
root ;


let map (D : Desc)(X : Set)(Y : Set)
        (f : X -> Y)(x : desc D X) : desc D Y ;
root ;