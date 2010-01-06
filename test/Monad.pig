make Nat := (Mu @ [`arg { zero, suc } [ (@ [`done]) (@ [`ind1 @ [`done]]) ] ] ) : * ;
make zero := [] : Nat ;
make suc := (\ x -> [x]) : Nat -> Nat ;
make one := (suc zero) : Nat ;
make two := (suc one) : Nat ;
make plus := @ @ [(\ r r y -> y) (\ r -> @ \ h r y -> suc (h y))] : Nat -> Nat -> Nat ;

make ExprD : Desc ;
give @ [`arg {num, add} [ ? ? ]] ;
  give @ [`arg Nat (\ n -> @ [`done])] ;
  give @ [`ind1 @ [`ind1 @ [`done]]] ; root ;

make Expr := (\ X -> Monad ExprD X) : * -> * ;

make var := (\ X x -> ' x) : (X : *) -> X -> Expr X ;
make num := (\ X n -> @ [`num n]) : (X : *) -> Nat -> Expr X ;
make add := (\ X a b -> @ [`add a b]) : (X : *) -> Expr X -> Expr X -> Expr X ;

make xplusy := add Nat (var Nat zero) (var Nat (suc zero)) : Expr Nat ;
make plus01 :=
  subst (ExprD, Nat, { }, num { }, xplusy) : Expr { } ;

make eval : Expr {} -> Nat ;
lambda t ;
give elimMonad(ExprD, {}, t, (\ x -> Nat), ?, ?) ;
give @ [ @ (\ n -> @ @ n) (\ t -> @ (\ x -> @ (\ y -> @ (plus x y)))) ] ;
give [] ; root ;

make main := eval plus01 : Nat
