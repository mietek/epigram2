let test1 {X : Set}{Y : Set}(f : X -> Y)(x : X) : Y ;
= f x ;
root ;

let test2 {X : Set}(Y : Set)(f : X -> Y)(x : X) : Y ;
= f x ;
root ;

let id {A : Set}(a : A) : A ;
= a ;
root ;

-- That's ok
let unif1 (X : Set)(x : X) : X ;
= test1./ X X id x ;
root ;

-- That's "type-checking failed"
let unif2 (X : Set)(x : X) : X ;
= test1 id x ;
root;

-- That's "type-checking failed"
let unif3 (X : Set)(x : X) : X ;
= test2 X id x ;
root;