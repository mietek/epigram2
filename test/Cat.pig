-- Ref.: "Computational Category Theory", Ryderheard, Burstall
--       [http://golem.ph.utexas.edu/category/2010/03/in_praise_of_dependent_types.html]


-- * Some Kit

-- ** Packing stuffs (avoid Sigma deconstruction)

data Pack (X : Set) := ( 'pack : X -> Pack X );

let unpackGen (X : Set)(C : Pack X) : X;
<= Pack.Ind X C;
define unpackGen _ ('pack sig) := sig;
root;

-- * Category

module Cat;

lambda Objs : Set;
lambda Arrs : (X : Objs)(Y : Objs) -> Set;

-- ** Definition

{-

  A category is composed by a set of objects |Obj| and arrows |Arr|,
  from objects -- |dom f| -- to objects -- |cod f|. Each object is
  equipped with an arrow from itself to itself -- |id_A|. Arrows can
  be composed: for any |f : A -> B| and |g : B -> C|, there exists an
  arrow |compos g f : A -> C|.

  Moreover, these objects satisfy two properties:
      * identity:
          for any |f : A -> B|,
	  |compos f (id_A)| == |compos (id_B) f| == 
      * associativity:
          for any |f : A -> B|, |g : B -> C|, |h : C -> D|,
	  |compos (compos h g) f == compos h (compos g f)|

-}

let CatSig : Set;
= Sig ( id : (X : Objs) -> Arrs X X 
      ; compos : (A : Objs)(B : Objs)(C : Objs)
                 (g : Arrs B C)(f : Arrs A B) ->
                 Arrs A C
      :- (X : Objs)(Y : Objs)(f : Arrs X Y) =>
         compos X X Y f (id X) == f
      :- (X : Objs)(Y : Objs)(f : Arrs X Y) =>
          compos X Y Y (id Y) f == f
      :- (A : Objs)(B : Objs)(C : Objs)(D : Objs)
         (f : Arrs A B)(g : Arrs B C)(h : Arrs C D) =>
         compos A B D (compos B C D h g) f == compos A C D h (compos A B C g f)
      ; ) ;
-- root;
-- jump Cat.CatSig;
out;

make Cat := Pack CatSig : Set;
make cat := \ c -> 'pack c : CatSig -> Cat;

make unpack := unpackGen CatSig : Cat -> CatSig ;

let id (C : Cat) : ((X : Objs) -> Arrs X X);
= (unpack C) ! ;
-- propsimpl;
-- root;
-- jump Cat.CatSig;
out;

let compos (C : Cat) : (A : Objs)(B : Objs)(C : Objs)
                       (g : Arrs B C)(f : Arrs A B) ->
                       Arrs A C;
= (unpack C) - ! ;
-- propsimpl;
-- root;
-- jump Cat.CatSig;
out;

{-
Doesn't quite work, I don't know why:

let pf-id-dom (C : Cat) : (:- ((X : Objs)(Y : Objs)(f : Arrs X Y) =>
                          compos X X Y f (id X) == f));

= (unpack C) - - ! ;
propsimpl;
root;
jump Cat.CatSig;
out;
-}

root;

-- ** Example: Category of Set

let SetCat : Cat.Cat Set (\ X Y -> (X -> Y));
= 'pack [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
-- Id:
    give \ X x -> x;

-- Compos:
    simpl;
    give g (f xf);

-- Pf-id-dom:
    propsimpl;
    next;

-- Pf-id-cod:
    propsimpl;
    next;

-- Pf-assoc:
    propsimpl;
root;

-- ** Example: Category of finite sets

let FinArr (dom : EnumU)(cod : EnumU) : Set;
= (Enum dom -> Enum cod);
root;

let FinCat : Cat.Cat EnumU FinArr;
= 'pack [ ?id ?compos ?pf-id-left ?pf-id-right ?pf-compos ];
-- Id:
   give \ X x -> x;

-- Compos:
    lambda A, B, C, g, f, x;
    give g (f x);

-- Pf-id-dom:
    propsimpl;
    next;

-- Pf-id-cod:
    propsimpl;
    next;

-- Pf-assoc:
    propsimpl;
root;

-- ** Example: Diagonal category

module DiagCat;

{-
 If you're a BSDM kind of person (you read this file, so you
 probably are), you could easily generalize that to the product of
 two categories.
-}

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

make unpack := Cat.unpack ObjsA ArrsA : Cat.Cat ObjsA ArrsA -> Cat.CatSig ObjsA ArrsA ;

-- *** Objects

-- Pairs of objects of A

let ObjsDiagA : Set;
= Sig (ObjsA ; ObjsA);
-- root;
-- jump DiagCat.ObjsDiagA;
out;

-- *** Arrows

-- Pairs of arrows of A

let ArrsDiagA (X : ObjsDiagA)(Y : ObjsDiagA) : Set;
= Sig ( ArrsA xf^1 xf ; ArrsA X Y );
root;
jump DiagCat.ObjsDiagA;
out;

-- *** Category:

let CatDiagA : Cat.Cat ObjsDiagA ArrsDiagA;
= 'pack [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
-- <1>.1 Id:
    simpl;
    give Cat.id ObjsA ArrsA CatA xf;
    give Cat.id ObjsA ArrsA CatA X;

-- <1>.2 Compos:
   simpl;
   give Cat.compos ObjsA ArrsA CatA xf^4 xf^3 xf^2 xf^1 xf;
   give Cat.compos ObjsA ArrsA CatA A B C g f;

-- <1>.3 Pf-id-dom:

--     <2>.1 Split X:
    lambda X;
    elim split ObjsA (\ _ -> ObjsA) X;
    lambda X1, X2;

--     <2>.2 Split Y:
    lambda Y;
    elim [Y] split ObjsA (\ _ -> ObjsA) Y;
    lambda Y1, Y2;

--     <2>.3 Split f:
    lambda f;
    elim [f] split (ArrsA X1 Y1) (\ _ -> ArrsA X2 Y2) f;
    lambda f1, f2;

--     <2>.4 Split the goal:
    propsimpl;

--         <3>.1 f1 o id = f1:
        give (unpack CatA - - !) X1 Y1 f1;

--         <3>.1 f2 o id = f2:
        give (unpack CatA - - !) X2 Y2 f2;

--     <2>.5 QED

-- <1>.4 Pf-id-cod: (really boring)

--     <2>.1 Split X:
    lambda X;
    elim split ObjsA (\ _ -> ObjsA) X;
    lambda X1, X2;

--     <2>.2 Split Y:
    lambda Y;
    elim [Y] split ObjsA (\ _ -> ObjsA) Y;
    lambda Y1, Y2;

--     <2>.3 Split f:
    lambda f;
    elim [f] split (ArrsA X1 Y1) (\ _ -> ArrsA X2 Y2) f;
    lambda f1, f2;

--     <2>.4 Split the goal:
    propsimpl;

--         <3>.1 id o f1 = f1:
        give (unpack CatA - - - !) X1 Y1 f1;

--         <3>.2 id o f2= f2:
        give (unpack CatA - - - !) X2 Y2 f2;

--         <3>.3 QED

--     <2>.5 QED

-- <1>.4 Pf-compos-cod: (really really boring)

--     <2>.1 Split A:
    lambda A;
    elim split ObjsA (\ _ -> ObjsA) A;
    lambda A1, A2;

--     <2>.2 Split B:
    lambda B;
    elim [B] split ObjsA (\ _ -> ObjsA) B;
    lambda B1, B2;

--     <2>.3 Split C:
    lambda C;
    elim [C] split ObjsA (\ _ -> ObjsA) C;
    lambda C1, C2;

--     <2>.4 Split D:
    lambda D;
    elim [D] split ObjsA (\ _ -> ObjsA) D;
    lambda D1, D2;

--     <2>.5 Split f:
    lambda f;
    elim [f] split (ArrsA A1 B1) (\ _ -> ArrsA A2 B2) f;
    lambda f1, f2;

--     <2>.6 Split g:
    lambda g;
    elim [g] split (ArrsA B1 C1) (\ _ -> ArrsA B2 C2) g;
    lambda g1, g2;

--     <2>.7 Split h:
    lambda h;
    elim [h] split (ArrsA C1 D1) (\ _ -> ArrsA C2 D2) h;
    lambda h1, h2;

--     <2>.8 Split the goal:
    propsimpl;

--         <3>.1 compos A1 B1 D1 (compos B1 C1 D1 h1 g1) f1 == 
--                 compos A1 C1 D1 h1 (compos A1 B1 C1 g1 f1)
        give (unpack CatA - - - - !) A1 B1 C1 D1 f1 g1 h1;

--         <3>.2 compos A2 B2 D2 (compos B2 C2 D2 h2 g2) f2 == 
--                  compos A2 C2 D2 h2 (compos A2 B2 C2 g2 f2)
        give (unpack CatA - - - - !) A2 B2 C2 D2 f2 g2 h2;

--         <3>.3 QED

--     <2>.9 QED

root;


-- ** Example: Fam I

module Fam;

lambda I : Set;

-- *** Objects

-- Objects are families of types

let ObjsFam : Set;
= I -> Set;
out;

-- *** Arrows

-- Point-wise morphisms in Set

let ArrsFam (X : ObjsFam)(Y : ObjsFam) : Set;
= (i : I) -> X i -> Y i;
out;

-- *** Category

let CatFam : Cat.Cat ObjsFam ArrsFam;
= 'pack [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
--    <1>.1 Id:
          give \ X i x -> x;
--    <1>.2 Compos:
          lambda A, B, C, g, f, i;
     	  give \ x -> g i (f i x);
--    <1>.3 Pf-id-dom:
          propsimpl;
	  next;
--    <1>.4 Pf-id-cod:
          propsimpl;
	  next;
--    <1>.5 Pf-assoc:
          propsimpl;
      

root;

-- ** Example: Slice category

module Slice;

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

lambda I : ObjsA;

make unpack := Cat.unpack ObjsA ArrsA : Cat.Cat ObjsA ArrsA -> Cat.CatSig ObjsA ArrsA ;

-- *** Objects

-- Morphisms J -> I for J an object of A

let ObjsSliceA : Set;
= Sig ( J   : ObjsA
      ; smap : ArrsA J I 
      ;);
out;

-- *** Arrows

-- Commuting triangles

let ArrsSliceA (X : ObjsSliceA)(Y : ObjsSliceA) : Set;
= Sig ( f : ArrsA J^1 J 
      :- ((unpack CatA) - !) J^1 J I smap f == smap^1 );
out;

-- *** Category:
let CatSliceA : Cat.Cat ObjsSliceA ArrsSliceA;
= 'pack [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
--     Give up now.

root;

-- * Functor
module Functor;

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

lambda ObjsB : Set;
lambda ArrsB : (X : ObjsB)(Y : ObjsB) -> Set;
lambda CatB : Cat.Cat ObjsB ArrsB;

-- ** Definition

{-

A functor F : A -> B from a category A to a category B is composed by:
    * an object part, mapping objects of A to objects of B
    * a morphism part, mapping morphisms of A to morphisms of B
such that:
    * F id_X == id_{F X}
    * F (compos g f) == compos (F g) (F f)

-}

let FunctorSig : Set;
= Sig ( obj : ObjsA -> ObjsB
      ; act : (X : ObjsA)(Y : ObjsA)(f : ArrsA X Y) -> 
              ArrsB (obj X) (obj Y)
      :- (X : ObjsA) =>
         act X X (Cat.id ObjsA ArrsA CatA X) == Cat.id ObjsB ArrsB CatB (obj X)
      :- (X : ObjsA)(Y : ObjsA)(Z : ObjsA)
         (f : ArrsA X Y)(g : ArrsA Y Z) =>
	 act X Z (Cat.compos ObjsA ArrsA CatA X Y Z g f) ==
	 Cat.compos ObjsB ArrsB CatB (obj X) (obj Y) (obj Z)
                    (act Y Z g) (act X Y f)
      ;);
-- root;
-- jump Functor.FunctorSig;
out;

make Functor := Pack FunctorSig : Set;

root;

-- ** Example: Identity functor

module IdFunctor;

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

make IdFunctorType := Functor.Functor ObjsA ArrsA CatA
                                      ObjsA ArrsA CatA : Set;

let IdFunctor : IdFunctorType;
= 'pack [ ?obj ?act ?pf-id ?pf-compos ];
-- Obj:
    give \ X -> X;

-- Act:
    give \ X Y f -> f;

-- Pf-id:
    propsimpl;
    next;

-- Pf-compos:
    propsimpl;
    

root;

-- ** Example: Diagonal functor

module DiagFunctor;

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

make ObjsDiagA := DiagCat.ObjsDiagA ObjsA ArrsA CatA : Set;
make ArrsDiagA := DiagCat.ArrsDiagA ObjsA ArrsA CatA : (X : ObjsDiagA)(Y : ObjsDiagA) -> Set;
make CatDiagA := DiagCat.CatDiagA ObjsA ArrsA CatA : Cat.Cat ObjsDiagA ArrsDiagA;



make DiagFunctorType := Functor.Functor ObjsA ArrsA CatA 
                                        ObjsDiagA ArrsDiagA CatDiagA : Set;


let DiagFunctor : DiagFunctorType;
= 'pack [ ?obj ?act ?pf-id ?pf-compos ];
-- Obj:
    give \ X -> [X , X ];

-- Act:
    give \ X Y f -> [f , f];

-- Pf-id:
    propsimpl;
    next;

-- Pf-compos:
    propsimpl;
    

root ;

-- * Appendix

{-
Local Variables:
mode: outline-minor
outline-regexp: "-- [*\f]+"
outline-level: outline-level
End:
-}
