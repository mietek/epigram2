make Nat := (Mu con ['arg (Enum ['zero 'suc]) [ (con ['done]) (con ['ind1 con ['done]]) ] ] ) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

make plus := con con [(\ r r y -> y) (\ r -> con \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;

make ExprD : Desc ;
give con ['arg (Enum ['num 'add]) [ ? ? ]] ;
  give con ['arg Nat (\ n -> con ['done])] ;
  give con ['ind1 con ['ind1 con ['done]]] ; root ;

make Expr := (\ X -> Monad ExprD X) : Set -> Set ;

make var := (\ X x -> ` x) : (X : Set) -> X -> Expr X ;
make num := (\ X n -> con ['num n]) : (X : Set) -> Nat -> Expr X ;
make add := (\ X a b -> con ['add a b]) : (X : Set) -> Expr X -> Expr X -> Expr X ;

make xplusx := add Nat (var Nat (suc zero)) (var Nat (suc zero)) : Expr Nat ;
make plus11 :=
  subst (ExprD, Nat, Enum [], num (Enum []), xplusx) : Expr (Enum []) ;

make eval : Expr (Enum []) -> Nat ;
lambda t ;
give elimMonad(ExprD, (Enum []), t, (\ x -> Nat), ?, ?) ;
give con [ con (\ n -> con con n) (\ t -> con (\ x -> con (\ y -> con (plus x y)))) ] ;
give [] ; root ;

make main := eval plus11 : Nat
