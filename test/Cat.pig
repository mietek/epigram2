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

make subst : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

-- * Category

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

let Cat (Objs : Set)(Arrs : (X : Objs)(Y : Objs) -> Set) : Set;
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
      ; );
root;

-- ** Example: Category of Set

let SetCat : Cat Set (\ X Y -> (X -> Y));
= [ ?id ?compos ?pf-id-dom ?pf-id-cod ?pf-assoc ];
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

let FinCat : Cat EnumU FinArr;
= [ ?id ?compos ?pf-id-left ?pf-id-right ?pf-compos ];
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


