let a : Set ;
root ;
scheme a ;

let f (X : Set)(x : X) : Set ;
root ;
scheme f;

let g {q : :- TT}(X : Set) : X ;
root ;
scheme g;

let h (X : Set){q : :- (FF => Inh X)} : X ;
root ;
scheme h;

let coe2 {S : Set}(T : Set){Q : :- S == T}(s : S) : T ;
lambda S, T, Q, s ;
= coe S T Q s ;
root ;