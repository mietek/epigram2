{-
Local Variables:
mode: outline-minor
outline-regexp: "-- [*\f]+"
outline-level: outline-level
End:
-}


-- Ref.: "Computational Category Theory", Ryderheard, Burstall
--       [http://golem.ph.utexas.edu/category/2010/03/in_praise_of_dependent_types.html]


-- * Some Kit

-- ** Substitution

make subst : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

-- ** Packing stuffs (avoid Sigma deconstruction)

data Pack (X : Set) := ( pack : X -> Pack X );

let unpack {X : Set}(C : Pack X) : X;
<= Pack.Ind X C;
define unpack _ ('pack sig) := sig;
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
      * associativity:
          for any |f : A -> B|, |g : B -> C|, |h : C -> D|,
	  |compos (compos h g) f == compos h (compos g f)|
      * identity:
          for any |f : A -> B|,
	  |compos f (id_A)| == |compos (id_B) f| == |f|

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
root;
jump Cat.CatSig;
out;

make Cat := Pack CatSig : Set;
make cat := \ c -> 'pack c : CatSig -> Cat;

let id (C : Cat) : ((X : Objs) -> Arrs X X);
= (unpack C) ! ;
propsimpl;
root;
jump Cat.CatSig;
out;

let compos (C : Cat) : (A : Objs)(B : Objs)(C : Objs)
                       (g : Arrs B C)(f : Arrs A B) ->
                       Arrs A C;
= (unpack C) - ! ;
propsimpl;
root;
jump Cat.CatSig;
out;

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

lambda ObjsA : Set;
lambda ArrsA : (X : ObjsA)(Y : ObjsA) -> Set;
lambda CatA : Cat.Cat ObjsA ArrsA;

let ObjsDiagA : Set;
= Sig (ObjsA ; ObjsA);
root;
jump DiagCat.ObjsDiagA;
out;

let ArrsDiagA (X : ObjsDiagA)(Y : ObjsDiagA) : Set;
= Sig ( ArrsA xf^1 xf ; ArrsA X Y );
root;
jump DiagCat.ObjsDiagA;
out;

let CatDiagA : Cat.Cat ObjsDiagA ArrsDiagA;
= 'pack [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
-- Id:
    simpl;
    give Cat.id ObjsA ArrsA CatA xf^1;
    give Cat.id ObjsA ArrsA CatA X;

-- Compos:
   simpl;
   give Cat.compos ObjsA ArrsA CatA xf^5 xf^4 xf^3 xf^2 xf^1;
   give Cat.compos ObjsA ArrsA CatA A B C g f;

-- Pf-id-dom: Holy shit!
   next;

-- Pf-id-cod: same story
   next;

-- Pf-assoc: give up

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
root;
jump Functor.FunctorSig;
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
