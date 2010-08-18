-- * Record definitions: 

make empty := REmpty : RSig ;
make one := (RCons REmpty 'one (\ _ -> Sig ())) : RSig ;
make two := RCons (RCons REmpty 'two (\ _ -> Enum ['a 'b])) 
     	    	 'one (\ _ -> (Enum ['c 'd 'e])) : RSig ;

-- * Example of records:

make x := [ [ _ , 'a ] , 'c ] : Record two;
make y := [ [ _ , 'a ] , 'e ] : Record two;


-- * Operators:

-- Intepretation:
infer Record;
-- Grab all labels:
infer labels;
-- Chunck types before, at label:
infer typeAt;
-- Get components before label:
infer fsts;
-- Access at label:
infer at;

-- * Tests:

make empty := REmpty : RSig ;
make cons := \ s i t -> RCons s i t :  (S : RSig) -> UId -> (Record S -> Set) -> RSig ;

elab labels two;
elab labels one;

elab typeAt two 'one;
elab typeAt two 'two;

elab fsts two 'two x;
elab fsts two 'one y;
elab fsts two 'two y;
elab fsts two 'one y;

elab at two 'one x;
elab at two 'two x;
elab at two 'one y;
elab at two 'two y;

-- * Dream:

{-

  There ought to be a Tactics.Record, but in the meantime, I thought I
  could build a set of (continuation-based) combinators to build
  "naturally" the records. This involves reversing the left-nesting.

  I use to do these things with polymorphism in Haskell, but here with
  type dependency, that doen't work through. We get into higher-order
  unification problem, if I understand correctly.

-}

let field {a : RSig -> Set}(S : RSig)(l : UId)(A : Record S -> Set)(k : (S : RSig) -> a S) : a (RCons S l A);
= k (RCons S l A);
root;

let begin {a : RSig -> Set}(k : (S : RSig) -> a S) : a REmpty ;
= k REmpty;
root;

let end (S : RSig) : RSig;
= S;
root;


-- ** Test:

-- Blow up everywhere. You cannot fake polymorphism, Luke.
make test1 := begin 
     	      end : RSig;
-- I don't want to do that:
next;
give (\ _ -> RSig);
root ;

make test2 := begin 
     	      field 'one (\ _ -> Enum ['a 'b])
	      end : RSig;
-- I don't want to suffer that:
next;
root;

make test3 := begin 
     	      field 'one (\ _ -> Enum ['a 'b])
	      field 'two (\ _ -> Enum ['c 'd])
	      end : RSig;
-- Nor that:
next;
root;

-- ** Target was:

{-

lambda Objs : Set;
lambda Arrs : (X : Objs)(Y : Objs) -> Set;

make cat := field 'id     ((X : Objs) -> Arrs X X)
     	   (field 'compos (\ id -> 
	   	  	    (A : Objs)(B : Objs)(C : Objs)
                            (g : Arrs B C)(f : Arrs A B) ->
                            Arrs A C)
	   (field 'pf-id-left (\ id compos ->
	   	  	       :- (X : Objs)(Y : Objs)(f : Arrs X Y) =>
			          compos X X Y f (id X) == f)
	   (field 'pf-id-right (\ id compos _ ->
	   	  	        :- (X : Objs)(Y : Objs)(f : Arrs X Y) =>
				   compos X Y Y (id Y) f == f)
	   (field 'pf-compos (\ id compos _ _ ->
                              :- (A : Objs)(B : Objs)(C : Objs)(D : Objs)
                              (f : Arrs A B)(g : Arrs B C)(h : Arrs C D) =>
                              compos A B D (compos B C D h g) f == 
			      compos A C D h (compos A B C g f)) 
	    end))))
-}

{-
Local Variables:
mode: outline-minor
outline-regexp: "-- [*\f]+"
outline-level: outline-level
End:
-}