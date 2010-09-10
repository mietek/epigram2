{-
  When we construct data types, we tend to produce tagged
  descriptions, i.e. those that start with a finite sum of
  possible constructors. These admit induction principles
  in a nicer form than that given by the standard machinery.
  Let's derive such induction principles generically.
-}

make TagDesc := Sig (E : EnumU ; Enum E -> Desc) : Set ;
make toDesc := (\ t -> 'sumD (t !) (t -)) : TagDesc -> Desc ;
make toSet := (\ t -> Mu (toDesc t)) : TagDesc -> Set ;

make DescInd := induction DescD : (v : Desc)(P : Desc -> Set)(p : (x : desc DescD Desc) -> box DescD Desc P x -> P (con x)) -> P v ;

{-
  The methods for the induction principle are a set of branches
  (giving a tuple) rather than a function from an enumeration;
  they are given by the following set.
-}

let Bits (T : TagDesc)(P : toSet T -> Set) : Set ;
= branches E (\ e -> ?) ;
give (x : desc (T e) (toSet [E , T])) -> box (T e) (toSet [E , T]) P x -> P (con [e , x]) ;
root ;

{-
  We will need a mapBox-like gadget that changes the predicate.
  This is a straightforward induction on descriptions.
-}

let boxer (X : Set)(P : X -> Set)(Q : X -> Set)(q : (y : X) -> P y -> Q y)(D : Desc)(x : desc D X)(b : box D X P x) : box D X Q x ;
<= DescInd D ;
define boxer X P Q q 'idD x b := q x b ;
define boxer X P Q q ('sumD E F) [c , x] b := boxer X P Q q (F c) x b ;
define boxer X P Q q ('prodD u E F) [a , b] [c , d] := [(boxer X P Q q E a c) , (boxer X P Q q F b d)] ;
define boxer X P Q q ('sigmaD E F) [s , x] b := boxer X P Q q (F s) x b ;
define boxer X P Q q ('piD S T) x b := \ s -> boxer X P Q q (T s) (x s) (b s) ;
root ;

{-
  Now we can define the nicer induction principle.
-}

make Ind : (T : TagDesc)(v : toSet T)(P : toSet T -> Set)(p : Bits T P) -> P v ;
simplify ;
elim induction (toDesc [E , T]) v ;
give \ E T -> con \ e x b P p -> ? ;
give switch E e (\ e -> ((x : desc (T e) (toSet [E , T])) -> box (T e) (toSet [E , T]) P x -> P (con [e , x]))) p x ? ;
give boxer (toSet [E , T]) (\ v -> ((P : toSet [E , T] -> Set)(p : branches E (\ e -> ((x : desc (T e) (toSet [E , T])) -> box (T e) (toSet [E , T]) P x -> P (con [e , x])))) -> P v)) P ?q (T e) x b ;
simplify ;
give xf P p ;
root ;

{-
  Let's see an example. We define a tagged description version of
  Nat by hand, but the data tactic could easily generate this.
-}

make NatTDesc := [ ['zero 'suc] , [('constD (Sig ())) ('prodD 'n 'idD ('constD (Sig ())))]] : TagDesc ;
make Nat := Mu (toDesc NatTDesc) : Set ;
make NatInd := Ind NatTDesc : (n : Nat)(P : Nat -> Set)(p : Bits NatTDesc P) -> P n ;

{-
  Note that when we eliminate by the induction principle, we have
  to provide a pair of methods, one for each constructor. This
  means problem simplification would not need to switch on
  enumerations automatically.
-}

let plus (m : Nat)(n : Nat) : Nat ;
elim NatInd m ;
give [? , ?] ;
simplify ;
define plus 'zero n := n ;
simplify ;
define plus ('suc m) n := 'suc (plus m n) ;
root ;
elab plus ('suc ('suc 'zero)) ('suc ('suc 'zero)) ;
