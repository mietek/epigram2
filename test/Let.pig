let a : Set ;
root ;
scheme a ;

let f (X : Set)(x : X) : Set ;
root ;
scheme f ;

let g {q : :- TT}(X : Set) : X ;
root ;
scheme g ;

let h (X : Set){q : :- (FF => Inh X)} : X ;
root ;
scheme h ;

let coe2 {S : Set}(T : Set){Q : :- S == T}(s : S) : T ;
-- = coe S T Q s ;
= s ;
root ;

let id {X : Set}(x : X) : X ;
= x ;
root ;

make A := ? : Set ;
make a := ? : id A ;
elab a ;
infer a ;
make b := ? : id./ _ A ;
elab b ;
infer b ;
make c := ? : id./ Set Set ;
elab c ;
infer c ;
make d := ? : id Set ;
elab d ;
infer d ;