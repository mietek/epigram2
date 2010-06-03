module X ;
lambda A : Set ;
make f := ? : Set ;
make f : A -> A ;
lambda a ;
make g : Set ;
root ; 
show state ;

elab X.f^1 ;
infer X.f^1 ;
elab X.f ;
infer X.f ;
elab X.f.g ;
infer X.f.g ;
elab X ;

in ;

show hyps ;
show context ;

elab f^1 ;
infer f^1 ;
elab f ;
infer f ;
elab f.g ;
infer f.g ;
elab X.f ;
infer X.f ;
elab X.f_1 ;
infer X.f_1 ;
elab X ;

in ;

show hyps ;
show context ;

elab f^1 ;
infer f^1 ;
elab X.f ;
infer X.f ;
elab X.f^1 ;
elab X.f_1 ;

elab g ;
infer g ;
elab f.g ;
infer f.g ;
elab X.f_1.g ;
infer X.f_1.g ;


