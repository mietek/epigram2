make P := ? : Prop ;
make Q := ? : Prop ;
make R := ? : Prop ;
make A := ? : Set ;
make B := ? : Set ;

make x : :- ((P => FF) => P => (X : Set) -> FF) ;
propsimplify ; -- Solve
root ;

make p : :- (P && (P => FF)) ;
propsimplify ; -- Absurd
root ;

make yes : :- ((P && (P => FF)) => FF) ;
propsimplify ; -- Solve
root ;

make yes2 : :- (P => (P => FF) => FF) ;
propsimplify ; -- Solve
root ;

make no : :- (((P => FF) && P) => FF) ;
propsimplify ; -- Solve
root ;

make nor : :- ((P => FF) => (P => FF)) ;
propsimplify ; -- Solve
root ;

make oor : :- ((P && (P => Q)) => FF) ;
propsimplify ; -- Simplify to P => Q => FF
root ;

make easy : :- TT ;
propsimplify ; -- Solve
root ;

make hard : :- FF ;
propsimplify ; -- Absurd
root ;

make useless : :- (TT => P) ;
propsimplify ; -- Simplify to P
root ;

make easyish : :- (FF => P) ;
propsimplify ; -- Solve
root ; 

make andy : :- (TT && P && TT) && (TT && Q) ;
propsimplify ; -- Simplify to P, Q
root ;

make ethel : :- (TT && P => Q && FF) ;
propsimplify ; -- Simplify to P => FF
root ;

make oops1 : :- ((TT && P => FF) => FF) ;
propsimplify ; -- Simplify to (P => FF) => FF
root ;

make oops2 : :- ((TT && P => Q && FF) => FF) ;
propsimplify ; -- Simplify to (P => FF) => FF
root ;

make f : :- ((TT => P) => TT) ;
propsimplify ; -- Solve
root ;

make g : :- (TT => TT) ;
propsimplify ; -- Solve
root ;

make h : :- (P => TT) ;
propsimplify ; -- Solve
root ;

make k : :- (P => FF && P) ;
propsimplify ; -- Simplify to P => FF
root ; 

make x : :- (((P && TT) && (TT && Q)) && R && P) ;
propsimplify ; -- Simplify to P, Q, R
root ;

make y : :- ((x : Set)(y : Set) -> TT) ;
propsimplify ; -- Solve
root ;

make z : :- ((x : Set) -> TT && P && Q) ;
propsimplify ; -- Simplify to Set -> P, Set -> Q
root ;

make a : :- ((TT => FF) => P) ;
propsimplify ; -- Solve
root ;

make b : :- (TT => TT && P) ;
propsimplify ; -- Simplify to P
root ;

make eek : :- ((P => FF) => FF) ;
propsimplify ; -- Stuck
root ;

make d : :- (P && Q => TT) ;
propsimplify ; -- Solve
root ;

make e : :- (TT && P => Q && TT) ;
propsimplify ; -- Simplify to P => Q
root ;

make f : :- (P => P) ;
propsimplify ; -- Solve
root ;

make g : :- (P && Q => R && Q && P) ;
propsimplify ; -- Simplify to P => Q => R
root ;

make h : :- ((P => Q) => P => Q) ;
propsimplify ; -- Solve
root ;

make h2 : :- (P => (P => Q) => Q) ;
propsimplify ; -- Solve
root ;

make k : :- (P == Q => P == Q) ;
propsimplify ; -- FAIL: Solve (eqUnfold needs fixing for Prop)
root ;

make l : :- (P => Q) ;
propsimplify ; -- Stuck
root ;

make m : :- ((: Set) Set == (: Set) Set) ;
propsimplify ; -- Solve
root ;

make p : :- (((: Set -> Prop) \ x -> P) == ((: Set -> Prop) \ x -> Q)) ;
propsimplify ; -- FAIL: Simplify to (X : Set) -> P == Q
root ;

make q : :- ((: Set) Set == (: Set) (Set -> Set)) ;
propsimplify ; -- Absurd
root ;

make q2 : :- (((: Set) Set == (: Set) (Set -> Set)) => P) ;
propsimplify ; -- Solve
root ;

make r : :- (P == P) ;
propsimplify ; -- Solve
root ;

make s : :- (A == A) ;
propsimplify ; -- Solve
root ;

make t : :- (A == B) ;
propsimplify ; -- Stuck
root ;

make x := ? : Sig (A ; B) ;
make y := ? : Sig (A ; B) ; 
make u : :- x == y ;
propsimplify ; -- Simplify to x ! == y !, x - == y -
root ;

make v : :- (P => (x : :- P)(y : :- P) -> x == y) ;
propsimplify ; -- Solve
root ;

make g := ? : (:- P) -> Prop ;
make w : :- ((x : :- P) -> g x) ;
propsimplify ; -- Stuck
root ;

make en : :- ((x : Enum ['a 'b 'c]) -> P) ;
propsimplify ; -- FAIL: Simplify to P?
root ;

make en2 : :- ((x : Enum ['a 'b]) -> x == (: Enum ['a 'b]) 'a) ;
propsimplify ; -- FAIL: Absurd?
root ;

make sf : :- ((x : A) -> FF) ;
propsimplify ; -- Stuck
root ;

make sf2 : :- ((x : A) -> FF && TT) ;
propsimplify ; -- Simplify to A -> FF
root ;

make sp : :- ((x : A) -> P) ;
propsimplify ; -- Stuck
root ;

make bug74 : :- (((x : A) -> (FF && FF)) => (FF && FF)) ;
propsimplify ; -- Simplify to (A -> FF) => FF
root ;

make sss : :- ((x : A) -> P && Q) ;
propsimplify ; -- Simplify to A -> P, A -> Q
root ;

make S := ? : A -> Prop ;
make T := ? : A -> Prop ;
make eee : :- ((a : A) -> S a && T a) ;
propsimplify ; -- Simplify to (a : A) -> A a, (a : A) -> T a
root ;

