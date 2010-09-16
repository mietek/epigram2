load TaggedInduction.pig ;

module IDesc ;
lambda I : Set ;
make Case := TData.tcase (Sig ()) [ IDescConstructors (\ _ -> IDescBranches I) ] [] : _ ;
make Ind := TData.tind (Sig ()) [ IDescConstructors (\ _ -> IDescBranches I) ] [] : _ ;
root ;


let BH (I : Set)
       (D : I -> IDesc I)
       (Q : (i : I)(v : IMu I D i) -> Set)
       (X : IDesc I)
       (y : idesc I X (\ i -> IMu I D i))
       (r : idesc (Sig (j : I ; IMu I D j)) (ibox I X (\ j -> IMu I D j) y)
         (\ a -> ((Q : (i : I)(v : IMu I D i) -> Set) -> Set)))
       : Set ;
refine BH I D Q X y r <= IDesc.Ind I X ;
refine BH I D Q ('varD j) y r = Sig (r Q ; Q j y) ;
refine BH I D Q ('constD C) y _ = Sig () ;
refine BH I D Q ('piD S T) y r = (s : S) -> BH I D Q (T s) (y s) (r s) ;
refine BH I D Q ('fpiD E T) y r = (e : Enum E) -> BH I D Q (T e)
    (switch E e (\ e -> idesc I (T e) (\ i -> IMu I D i)) y)
    (switch E e (\ e -> idesc (Sig (j : I ; IMu I D j)) (ibox I (T e) (\ j -> IMu I D j) (switch E e (\ f -> idesc I (T f) (\ j -> IMu I D j)) y)) (\ a -> ((Q : (i : I)(v : IMu I D i) -> Set) -> Set))) r) ;
refine BH I D Q ('sigmaD S T) [s , y] r = BH I D Q (T s) y r ;
refine BH I D Q ('fsigmaD E T) [e , y] r = BH I D Q
    (switch E e (\ e -> IDesc I) T) y r ;

{-
We need to do something like the following, but are unable to refer to
< BH ... > explicitly, so we need to find an alternative.

give switch E e (\ e -> ((D : I -> IDesc I)(Q : (i : I)(v : IMu I D i) -> Set)(y : idesc I (switch E e (\ f -> IDesc I) T) (\ i -> IMu I D i))(r : idesc (Sig (j : I ; IMu I D j)) (ibox I (switch E e (\ f -> IDesc I) T) (\ j -> IMu I D j) y) (\ a -> ((Q : (i : I)(v : IMu I D i) -> Set) -> Set)))(qsm : :- ((: Sig ()) []) == ((: Sig ()) [])) -> < BH I D Q (switch E e (\ f -> IDesc I) T) y r : Set >)) Th D Q y r _
-}

next ;

refine BH I D Q ('prodD u A B) [yA , yB] [rA , rB] = Sig (BH I D Q A yA rA ; BH I D Q B yB rB) ;
root ;


make Below : (I : Set)(D : I -> IDesc I)(Q : (i : I)(v : IMu I D i) -> Set)(i : I)(v : IMu I D i) -> Set ;
lambda I, D, Q, i, v ;
elim iinduction I D i v ;
lambda I, D, i, y, r, Q ;
give BH I D Q (D i) y r ;
root ;


let genHelp (I : Set)
    	    (D : I -> IDesc I)
            (Q : (i : I) -> IMu I D i -> Set)
	    (body : (i : I)(x : IMu I D i)(below : Below I D Q i x) -> Q i x)
       	    (X : IDesc I)
       	    (y : idesc I X (\ i -> IMu I D i))
       	    (r : idesc (Sig (j : I ; IMu I D j))
	        (ibox I X (\ j -> IMu I D j) y) 
		(\ a -> ((Q : (i : I) -> IMu I D i -> Set)
		         (body : (i : I)(x : IMu I D i)
			           (below : Below I D Q i x) -> Q i x)
                          -> Below I D Q (a !) (a -))))
       	    : BH I D Q X y
	        (imapBox I X (\ j -> IMu I D j)
		    (\ a -> ((Q : (i : I)(v : IMu I D i) -> Set) -> Set))
		    (\ a Q -> Below I D Q (a !) (a -)) y) ;

{-
For some reason, this gives an unknown error:

refine genHelp I D Q body X y r <= IDesc.Ind I X ;
-}

root ;

make gen : (I : Set)
     	   (D : I -> IDesc I)
           (Q : (i : I) -> IMu I D i -> Set)
	   (body : (i : I)(x : IMu I D i)(below : Below I D Q i x) -> Q i x)
	   (i : I)
	   (x : IMu I D i)
	   -> Below I D Q i x ;
lambda I, D, Q, body, i, x ;
elim iinduction I D i x ;
lambda I, D, i, x, y, Q, body ;
give genHelp I D Q body (D i) x y ;
root ;


let Fix (I : Set)(D : I -> IDesc I)(i : I)(x : IMu I D i)(Q : (i : I) -> IMu I D i -> Set)(m : (i : I)(x : IMu I D i) -> Below I D Q i x -> Q i x) : Q i x ;
refine Fix I D i x Q m = m i x (gen I D Q m i x) ;
root ;

