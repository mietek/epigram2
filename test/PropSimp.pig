make P := ? : Prop ;
make Q := ? : Prop ;
make R := ? : Prop ;

make easy : :- TT ;
simplify ;

make hard : :- FF ;
simplify ;
root ;

make useless : :- (TT => P) ;
simplify ;
root ;

make easyish : :- (FF => P) ;
simplify ;

make andy : :- (TT && P && TT) && (TT && Q) ;
simplify ;
simplify ;
root ;

make ethel : :- (TT && P => Q && FF) ;
simplify ;
root ;

make oops : :- ((TT && P => Q && FF) => FF) ;
simplify ;