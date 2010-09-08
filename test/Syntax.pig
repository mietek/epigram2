{-
                            Epigram Syntax
-}

{-

    This is a guided tour into Epigram syntax. Syntax is a strong
    word, I would personally call that a random set of hieroglyphic
    symbols. Hence this file.

                                                  Champollion.

-}

-- * The world of Set

make set := Set : Set;

-- ** Pi-types

make pi1 := (x : Set) -> Set : Set;
make pi2 := (x : Set)(y : Set) -> Set : Set;
make pi3 := (x : Set) -> Set -> Set : Set;
make pi4 := (x : Set) -> Set -> (y : Set) -> Set : Set;
-- No: make pi5 := (x y : Set) -> Set : Set; 
make pi6 := (x : Set)(_ : Set) -> Set : Set;
-- For perverts:
make pi7 := Pi Set (\ x -> Set) : Set;

-- ** Lambda

make lambda1 := \ x -> x : Set -> Set;
-- No: make lambda2 := \x -> x : Set -> Set;
make lambda3 := \ x -> \ y -> x : Set -> Set -> Set;
make lambda4 := \ x y -> x : Set -> Set -> Set;
make lambda5 := \ x _ -> x : Set -> Set -> Set;

-- ** Sigma-types

-- Unit:
make sigma1 := Sig () : Set;

make sigma2 := Sig ( Set ; Set ) : Set;
make sigma3 := Sig ( Set ; Set ;) : Set;
make sigma4 := Sig ( X : Set ; X ) : Set;
make sigma5 := Sig ( X : Set ; b : X ; ) : Set;

-- Packing proofs (specifications)
make sigma6 := Sig ( Set :- TT ) : Set;
make sigma7 := Sig ( X : Set :- TT) : Set;
make sigma8 := Sig ( X : Set :- TT :- FF ) : Set;

-- For perverts again:
make sigma9 := Sig Set (\ _ -> Set) : Set;

-- *** Tuple

-- Void:
make tuple1 := [] : Sig ();

make tuple2 := [Set , Set] : Sig (Set ; Set );

make tuple3 := [Set , [Set , []]] : Sig (Set ; Set ; Sig ());
make tuple4 := [Set , [Set , []]] : Sig (Set ; Set ;);
-- Lisp convention: [a b c] == [a , [b , [c , []]]]
make tuple5 := [Set Set] : Sig (Set ; Set ;);

-- With proofs:
make sigma10 := Sig ( Set :- TT ) : Set;
make tuple6 := [ Set , [] ] : sigma10;
-- No: make tuple7 := [ Set [] ] : sigma10;

-- *** Projections

make proj1 := \ x -> x ! : Sig ( (Enum ['a 'b]) ; (Enum ['c 'd]) ) -> (Enum ['a 'b]);
make proj2 := \ x -> x - : Sig ( (Enum ['a 'b]) ; (Enum ['c 'd]) ) -> (Enum ['c 'd]);
-- No: make proj3 := \ x -> x - - : Sig ( Set ; Set ) -> Sig ();
make proj4 := \ x -> x - - : Sig ( Set ; Set ; Set ) -> Set ;
-- No? make proj5 := \ x -> x -- : Sig ( Set ; Set ; Set ) -> Set ;
make proj6 := \ x -> x - - : Sig ( Set ; Set ; ) -> Sig ();

-- *** Function space on Sigmas

-- When the domain is a |Sig A|, the elaborator accept the |con| of a
-- function which type is a |Pi A|:
make funs1 := con (\ x -> x) : Sig () -> Set -> Set;
make funs2 := con (\ x y z -> x) : Sig ( Set ; Set ) -> Set -> Set ;

-- ** UId

make uid1 := UId : Set;
make uid2 := 'a : UId;
make uid3 := 'aristotle : UId;

-- ** Enumerations

make enum1 := ['a 'b 'c ] : EnumU;
make enum2 := \ e -> Enum e : EnumU -> Set;

make enumT1 := Enum ['a 'b 'c] : Set;
make enumT2 := Enum ['a 'b 'c] : Set;
make enumT3 := Enum [] : Set;

-- *** Indexing by position

-- Index 'a:
make enum3 := 0 : Enum ['a 'b 'c];
-- Index 'b:
make enum4 := 1 : Enum ['a 'b 'c];
-- Index 'c
make enum5 := 2 : Enum ['a 'b 'c];
-- No: make enum6 := 3 : Enum ['a 'b 'c];

-- *** Indexing by name

make enum7 := 'a : Enum ['a 'b 'c];
make enum8 := 'b : Enum ['a 'b 'c];
make enum9 := 'c : Enum ['a 'b 'c];

-- *** Relative indexing

-- Index 'b
make enum10 := 1 + 1 : Enum ['a 'b 'c];
make enum11 := \ x -> 1 + x : Enum ['b 'c] -> Enum ['a 'b 'c];

-- *** Finite function space

-- We write a tuple covering each cases, instead of a lambda and
-- appeal to |switch|

make enum12 := [(Enum ['e 'f 'g]) (Enum ['i 'k 'l 'm])] : Enum ['a 'b] -> Set;
make enum13 := ['f 'm] : (x : Enum ['a 'b]) -> enum12 x;


-- ** Type annotation

infer (: Set) Set;
infer (: Enum ['a 'b 'c]) 'a;

-- ** Joker

make joker1 := _ : Sig ();

-- ** Question mark

make qmark1 := ? : Sig (); 
next;
give _ ;
root;
make qmark2 := ?name : Sig ();
next;
give _ ;
root;

-- ** Con / Out

{-

  Con is very general container, used all over the place to pack stuff
  up. However, I cannot think of a non-contrived example of its
  use. If someone have an idea, please write something.

  While con packs things up, Out -- written '%' -- unpacks
  containers. Again, I cannot think of a simple example right away.

-}

-- make con1 := con ? : ? 
-- make out1 := ? % : Set

-- * The world of Prop

make prop1 := Prop : Set;

-- ** Trivial, Absurd, And

make tf1 := TT : Prop;
make tf2 := FF : Prop;
make tf3 := TT && TT : Prop;
make tf4 := TT && FF : Prop;

-- ** Proofs in Set

make pf1 := :- TT : Set;
make pf2 := :- FF : Set;

make pf3 := [] : :- TT;
make pf4 := _ : :- TT;

-- The *only* eliminator over Prop
make pf5 := naughtE : :- FF -> (A : Set) -> A;

-- ** All

make all1 := All Set (\ _ -> TT) : Prop;
make all2 := All Set (\ X -> All X (\ _ -> TT)) : Prop;
make all3 := (X : Set) => TT : Prop;
make all4 := (X : Set)(y : X) => TT : Prop;
-- No: make all5 := (x : Set) => Set => TT : Prop;
-- No: make all6 := (x : Set) => Set => (y : Set) => TT : Prop;
-- No: make all7 := (x y : Set) => TT : Prop; 
make all8 := (x : Set)(_ : Set) => TT : Prop;

-- ** Implication 

make imp1 := TT => FF : Prop;
make imp2 := TT => TT => FF : Prop;
make imp3 := (X : Set) => TT => FF : Prop;

-- ** Inh, Wit

-- I don't know how these things ought to be used.

-- * Equality

-- ** Blue equality

make eq1 := (A : Set)(x : A) => x == x : Prop;
make eq2 := (A : Set)(x : A)(y : A) => x == y : Prop;
make eq3 := (A : Set)(B : Set)(x : A)(y : B) => (: A) x == (: B) y : Prop;
make eq4 := (A : Set)(B : Set)(x : A)(y : B) => x == y : Prop;

-- ** Green equality

make geq1 := (S : Set)(s : S)(T : Set)(t : T) => eqGreen S s T t : Prop;

-- Blue to green
make geq2 := \ _ _ _ _ eq -> eq % : (S : Set)(s : S)(T : Set)(t : T) -> :- (s == t) -> :- (eqGreen S s T t);

-- ** Refl

make refl1 := refl : :- ((A : Set)(x : A) => x == x);

-- ** Operators

make coe1 := coe : (S : Set)(T : Set)
                   (q : :- S == T) -> S -> T;

make coh1 := coh : (X : Set)(Y : Set)
                   (q : :- X == Y)
                   (s : X) -> :- s == (coe X Y q s);
 
-- ** Substitution (example)

-- Often called |ship|, for bad reasons.

make subst := (\ X x y q P p ->
               coe (P x) (P y) (con (((: :- P == P) _)
                                % x y _)) p)
           : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;


-- * Data-type definitions

data Nat := ('zero : Nat) 
          ; ('suc : Nat -> Nat);

-- No: data Nat := ('zero : Nat) ;
--                 ('suc : Nat -> Nat);
-- because an end-of-line is a ";"

data List (X : Set) := ('nil : List X) 
                     ; ('cons : X -> List X -> List X);

data Tree (X : Set) := ('leaf : Tree X) 
                     ; ('node : X -> Tree X -> Tree X -> Tree X);

-- ** Inhabitants of data-types

make ze1 := 'zero : Nat;
make ze2 := con ['zero] : Nat;
make ze3 := con ['zero , []] : Nat;
make su1 := \ n -> 'suc n : Nat -> Nat;
make su2 := \ n -> con [ 'suc n ] : Nat -> Nat;

-- * Programming problems

let pbm1 (A : Set) : Set;
undo;
let pbm2 (A : Set)(b : A) : Set;
undo;

-- Implicit argument:
let pbm3 {A : Set}(b : A) : Set;
undo;


{-
Local Variables:
mode: outline-minor
outline-regexp: "-- [*\f]+"
outline-level: outline-level
End:
-}
