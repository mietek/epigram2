-- Ref.: "Computational Category Theory", Ryderheard, Burstall

make subst : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;


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

let Cat (Obj : Set)(Arr : Set) : Set;
= Sig ( dom : Arr -> Obj
      ; cod : Arr -> Obj
      ; id : Obj -> Arr
      ; compos : (g : Arr)(f : Arr) -> :- (cod f == dom g) -> Arr
      :- (f : Arr)(g : Arr)(h : Arr) => 
         cod f == dom g && cod g == dom h =>
         compos (compos h g) f == compos h (compos g f)
      :- (f : Arr) =>
         compos f (id (dom f)) == f &&
	 compos (id (cod f)) f == f 
      ; );
root;

{-
-- Example: Category of Set
let SetArr : Set;
= Sig ( dom : Set
      ; cod : Set
      ; f : dom -> cod
      ;);
root;

let SetDom (arr : SetArr) : Set;
= dom;
root;

let SetCod (arr : SetArr) : Set;
= cod;
root;

let SetMap (arr : SetArr) : (SetDom arr) -> (SetCod arr);
= f;
root;

let SetCompos (g : SetArr)(f : SetArr)(p : :- SetCod f == SetDom g) : SetArr;
= [ dom cod^1 (\ x -> f^1 (f x))];
root;

{-
make Set-pf-assoc : (f : SetArr)(g : SetArr)(h : SetArr)
                    (pf-g-o-f : :- SetCod f == SetDom g)
                    (pf-h-o-g : :- SetCod g == SetDom h) ->
                    :- SetCompos (SetCompos h g pf-h-o-g) f pf-g-o-f  == SetCompos h (SetCompos g f pf-g-o-f) pf-h-o-g;
-}

{-


let SetCat : Cat Set SetArr;
= [ ?dom ?cod ?id ?compos ?pf-compos ?pf-id ];
-- Dom:
    give SetDom;

-- Cod:
   give SetCod;

-- Id:
    lambda X;
    give [ X X (\ x -> x) ];

-- Compos:
    lambda g, f, eq;
    give [ (SetDom f) (SetCod g) (\ x -> (SetMap g) ((SetMap f) x)) ];
-}   

-- root;

{-
-- Example: Category of finite sets

let FinArr : Set;
= Sig ( dom : EnumU
      ; cod : EnumU
      ; f : Enum dom -> Enum cod 
      ;);
root;

let FinDom (arr : FinArr) : EnumU;
= dom;
root;

let FinCod (arr : FinArr) : EnumU;
= cod;
root;

let FinMap (arr : FinArr) : Enum (FinDom arr) -> Enum (FinCod arr);
= f;
root;

let FinCat : Cat EnumU FinArr;
= [ ?dom ?cod ?id ?compos ?pf-compos ?pf-id ];
-- Dom:
    give FinDom;

-- Cod:
    give FinCod;

-- Id:
    lambda X;
    give [ X X (\ x -> x) ];

-- Compos:
   lambda g, f, eq;
   give [ (FinDom f) (FinCod g) (\ x -> (FinMap g) ((FinMap f) x)) ];

-- Pf-compos:
   
-}