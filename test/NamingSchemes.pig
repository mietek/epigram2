module X ;
lambda A : Set ;

let f : Set ;
out ;
out ;

let f (a : A) : A ;
let g : Set ;

root ;

show state ;

elab X.f^1 ;
infer X.f^1 ;
scheme X.f^1 ;

elab X.f ;
infer X.f ;
scheme X.f ;

elab X.f.impl.g ;
infer X.f.impl.g ;
scheme X.f.impl.g ;

in ;

show hyps ;
show context ;

elab f^1 ;
infer f^1 ;
scheme f^1 ;
elab f ;
infer f ;
scheme f ;
elab f.impl.g ;
infer f.impl.g ;
scheme f.impl.g ;
elab X.f ;
infer X.f ;
scheme X.f ;
elab X.f_1 ;
infer X.f_1 ;
scheme X.f_1 ;

in ;
in ;

show hyps ;
show context ;

elab f^2 ;
infer f^2 ;
scheme f^2 ;
elab X.f ;
infer X.f ;
scheme X.f ;

elab g ;
infer g ;
scheme g ;
elab X.f_1.impl.g ;
infer X.f_1.impl.g ;
scheme X.f_1.impl.g ;



