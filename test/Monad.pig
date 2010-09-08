make Nat := Mu (con ['sigmaD (Enum ['zero 
                                    'suc]) 
                             [ (con ['constD (Sig ())]) 
			       (con ['prodD 'n (con ['idD]) (con ['constD (Sig ())]) ])]]) : Set ;
make zero := con ['zero] : Nat ;
make suc := (\ x -> con ['suc x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;

make plus := con con [(\ r r y -> y) (\ r -> con \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;

make ExprD : Desc ;
give con ['sigmaD (Enum ['num 'add]) [ ? ? ]] ;
  give con ['sigmaD Nat (\ n -> con ['constD (Sig ())])] ;
  give con ['prodD 'f (con ['idD]) (con ['prodD 'a (con ['idD]) (con ['constD (Sig ())])])] ; 
root ;

make Expr := (\ X -> Monad ExprD X) : Set -> Set ;

make var := (\ X x -> ` x) : (X : Set) -> X -> Expr X ;
make num := (\ X n -> con ['num n]) : (X : Set) -> Nat -> Expr X ;
make add := (\ X a b -> con ['add a b]) : (X : Set) -> Expr X -> Expr X -> Expr X ;

make xplusx := add Nat (var Nat (suc zero)) (var Nat (suc zero)) : Expr Nat ;
make plus11 :=
  substMonad ExprD Nat (Enum []) (num (Enum [])) xplusx : Expr (Enum []) ;

make eval : Expr (Enum []) -> Nat ;
lambda t ;
give elimMonad ExprD (Enum []) t (\ x -> Nat) ? ? ;
give con [ con (\ n -> con con n) (\ t -> con (\ x -> con (\ y -> con (plus x y)))) ] ;
give [] ; root ;

make main := eval plus11 : Nat ;
elab main
