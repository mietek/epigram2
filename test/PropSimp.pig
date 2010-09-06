make P := ? : Prop ;
make Q := ? : Prop ;
make R := ? : Prop ;
make A := ? : Set ;
make B := ? : Set ;

make easy : :- TT ;
propsimplify ;
root ;

make hard : :- FF ;
propsimplify ;
root ;

make useless : :- (TT => P) ;
propsimplify ;
root ;

make easyish : :- (FF => P) ;
propsimplify ;
root ; 

make andy : :- (TT && P && TT) && (TT && Q) ;
propsimplify ;
root ;

make ethel : :- (TT && P => Q && FF) ;
propsimplify ;
root ;

make oops : :- ((TT && P => Q && FF) => FF) ;
propsimplify ;
root ;

make f : :- ((TT => P) => TT) ;
propsimplify ;
root ;

make g : :- (TT => TT) ;
propsimplify ;
root ;

make h : :- (P => TT) ;
propsimplify ;
root ;

make k : :- (P => FF && P) ;
propsimplify ;
root ; 

make x : :- (((P && TT) && (TT && Q)) && R && P) ;
propsimplify ;
root ;

make y : :- ((x : Set)(y : Set) => TT) ;
propsimplify ; 
root ;

make z : :- ((x : Set) => TT && P && Q) ;
propsimplify ; 
root ;

make a : :- ((TT => FF) => P) ;
propsimplify ;
root ;

make b : :- (TT => TT && P) ;
propsimplify ;
root ;

make eek : :- ((P => FF) => FF) ;
propsimplify ;
root ;

make d : :- (P && Q => TT) ;
propsimplify ;
root ;

make e : :- (TT && P => Q && TT) ;
propsimplify ;
root ;

make f : :- (P => P) ;
propsimplify ;
root ;

make g : :- (P && Q => R && Q && P) ;
propsimplify ;
root ;

make h : :- ((P => Q) => P => Q) ;
propsimplify ;
root ;

make k : :- (P == Q => P == Q) ;
propsimplify ;
root ;

make l : :- (P => Q) ;
propsimplify ;
root ;

make m : :- ((: Set) Set == (: Set) Set) ;
propsimplify ; 
root ;

make p : :- (((: Set -> Prop) \ x -> P) == ((: Set -> Prop) \ x -> Q)) ;
propsimplify ;
root ;

make q : :- ((: Set) Set == (: Set) (Set -> Set)) ;
propsimplify ;
root ;

make r : :- (P == P) ;
propsimplify ;
root ;

make s : :- (A == A) ;
propsimplify ;
root ;

make t : :- (A == B) ;
propsimplify ;
root ;

make u : :- ((: Sig (A ; B)) ?x == (: Sig (A ; B)) ?y) ;
propsimplify ;
root ;

make v : :- (P => (x : :- P)(y : :- P) => x == y) ;
propsimplify ;
root ;

make g := ? : (:- P) -> Prop ;
make w : :- ((x : :- P) => g x) ;
propsimplify ;
root ;

make en : :- ((x : Enum ['a 'b 'c]) => P) ;
propsimplify ;
root ;

make en2 : :- ((x : Enum ['a 'b]) => x == (: Enum ['a 'b]) 'a) ;
propsimplify ;
root ;

make sf : :- ((x : A) => FF) ;
propsimplify ;
root ;

make sf2 : :- ((x : A) => FF && TT) ;
propsimplify ;
root ;

make sp : :- ((x : A) => P) ;
propsimplify ;
root ;

make bug74 : :- (((x : A) => (FF && FF)) => (FF && FF)) ;
propsimplify ;
root ;