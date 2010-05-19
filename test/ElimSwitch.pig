make e := ['a 'b 'c] : EnumU ;
make f : Enum e -> Set -> Set ;
lambda x ;
lambda y ; 
elim switch e x ;
out ;
out ;
show state ;