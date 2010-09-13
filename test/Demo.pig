{-
  Epigram: a dependently typed programming language

  This file is a demonstration of Cochon, the Epigram interactive interface that
  looks a bit like a programming language if you squint. Once you have built
  the system, start it by running "./Pig", then copy lines one at a time from
  this file to the prompt.

  If you use Emacs, run send-line.el, then open this file in one window and 
  a shell running Pig in the other window. You can then type C-c C-r to run
  the current line and C-c C-u to undo it.
-}

{-
  Bool is one of the simplest possible data types, with only two constructors.
-}

data Bool := ('false : Bool) ; ('true : Bool) ;

elab 'true : Bool ;
elab 'false : Bool ;





{-
  Natural numbers are a data type with two constructors: zero is a number, and
  every number has a successor. 
-}

data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;

elab 'zero : Nat ;
make one := 'suc 'zero : Nat ; elab one ;
make two := 'suc ('suc 'zero) : Nat ; elab two ;


{- 
  We can write functions to manipulate this data.
  The addition function, written in a pattern-matching style, looks like this:

    plus : Nat ->   Nat ->  Nat
    plus   zero     n    =  n
    plus   (suc k)  n    =  suc (plus k n)

  This definition is recursive (it refers to itself), so why does it make sense?
  In other words, why does evaluation of |plus k n| terminate? In fact, the
  definition is structurally recursive on the first argument, but the
  pattern-matching style hides this.

  Epigram requires programs to be total: general recursion is not allowed.
  The structural recursion is made explicit by appeal to the induction principle
  for natural numbers, here called Nat.Ind.
-}

let plus (m : Nat)(n : Nat) : Nat ;
refine plus m n <= Nat.Ind m ;
next ;
refine plus ('suc k) n = 'suc (plus k n) ;
root ;

{-
  Notice that we did not define plus for the case when the first argument is
  zero. We are allowed to leave "holes" in programs and fill them in later.
  Watch what happens when we try to execute plus:
-}

elab plus two two ;

{-
  Some computation is possible, but not all of it! Perhaps we should go back and
  fill in the missing line of the program:
-}

next ;
refine plus 'zero n = n ; 
root ;

{-
  Now we get the result we expect:
-}

elab plus two two ;



{-
  A major benefit of explicitly appealing to an induction principle is that we
  can invent our own, rather than being restricted to structural recursion.
  If we have two numbers x and y, we can eliminate them by comparison, provided
  we say what to do in three cases:
    l - x is less than y
    e - x and y are equal
    g - x is greater than y
-}

let compare (x : Nat)(y : Nat)(P : Nat -> Nat -> Set)(l : (x : Nat)(y : Nat) -> P x (plus x ('suc y)))(e : (x : Nat) -> P x x)(g : (x : Nat)(y : Nat) -> P (plus y ('suc x)) y) : P x y ;
refine compare x y P l e g <= Nat.Ind x ;

refine compare 'zero y P l e g <= Nat.Ind y ;
refine compare 'zero 'zero    P l e g = e 'zero ;
refine compare 'zero ('suc k) P l e g = l 'zero k ;

refine compare ('suc j) y P l e g <= Nat.Ind y ;
refine compare ('suc j) 'zero P l e g = g j 'zero ;
refine compare ('suc j) ('suc k) P l e g <= compare j k ;
refine compare ('suc j) ('suc (plus j ('suc k))) P l e g = l ('suc j) k ;
refine compare ('suc j) ('suc j) P l e g = e ('suc j) ;
refine compare ('suc (plus k ('suc j))) ('suc k) P l e g = g j ('suc k) ;
root ;


{-
  Now that we have our new induction principle, we can use it just like Nat.Ind.
  We already did this when explaining how to compare two successors. Here's a
  simpler example:
-}

let max (a : Nat)(b : Nat) : Nat ;
refine max a b <= compare a b ;
refine max a (plus a ('suc b)) = plus a ('suc b) ;
refine max a a = a ;
refine max (plus b ('suc a)) b = plus b ('suc a) ;
root ;

elab max two one ;
elab max 'zero one ;
elab max 'zero 'zero ;



{-
  The Curry-Howard correspondence is the observation that types correspond to
  mathematical theorems, and a program is a proof of a theorem. We can use this
  to state and prove theorems about our programs.

  For example, we can show that plus is commutative (independent of the order
  of its arguments):
-}

make plus-commutative := ? : :- ((k : Nat)(n : Nat) => plus k n == plus n k) ;

{-
  In fact, thanks to our model of equality we can prove a stronger result,
  which is not true in most other comparable systems: that the function
  |plus| is equal to |flip plus|.
-}

make flip := (\ f k n -> f n k) : (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat ;
make plus-function-commutative := ? : :- (flip plus == plus) ;

{-
  See Plus.pig in the Epigram tests directory for proofs of these theorems.
-}






{-
  Parameterised types such as lists are fundamental to functional programming.
  A list is either empty (nil) or a value followed by a list (cons).
-}

data List (A : Set) := ('nil : List A) ; ('cons : A -> List A -> List A) ;

elab 'nil : List Bool ;
elab 'cons 'true 'nil : List Bool ;
elab 'cons one ('cons two 'nil) : List Nat ;


{-
  What happens if we try to write a function to extract the first element of a
  list? There is nothing we can do in the nil case, so we just skip it.
-}

let head (A : Set)(as : List A) : A ;
refine head A as <= List.Ind A as ;
next ;
refine head A ('cons a _) = a ;
root ;


elab head Bool ('cons 'true 'nil) ;
elab head Bool ('cons 'false ('cons 'true 'nil)) ;
elab head Bool 'nil ;





{-
  There are many similar examples that arise in functional programming.
  How can we resolve this problem? Perhaps instead of using lists, we should
  work with vectors: lists indexed by their length. 

  In the following line, note that the natural number is an index, not a
  parameter: it varies depending on which constructor you choose.
-}

idata Vec (A : Set) : Nat -> Set := ('vnil : Vec A 'zero) ; ('vcons : (n : Nat) -> A -> Vec A n -> Vec A ('suc n)) ;

{-
  Now we can safely define the vector version of head. Since we ask for a vector
  of length at least one, we know we can always return a result.
-}

let vhead (A : Set)(n : Nat)(as : Vec A ('suc n)) : A ;
refine vhead A n as <= Vec.Ind A ('suc n) as ;
refine vhead A n ('vcons n a as) = a ;
root ;


elab vhead Bool 'zero ('vcons 'zero 'true 'vnil) ;
elab vhead Bool one ('vcons one 'false ('vcons 'zero 'true 'vnil)) ;




{-
  The vectorised application function takes a vector of functions and a vector
  of arguments, and applies the functions pointwise.
-}

let vapp (A : Set)(B : Set)(n : Nat)(fs : Vec (A -> B) n)(as : Vec A n) : Vec B n ;
refine vapp A B n fs as <= Vec.Ind (A -> B) n fs ;
refine vapp A B 'zero 'vnil as = 'vnil ;
refine vapp A B ('suc j) ('vcons j f fs) as <= Vec.Ind A ('suc j) as ;
refine vapp A B ('suc j) ('vcons j f fs) ('vcons j a as) = 'vcons j (f a) (vapp A B j fs as) ;
root ;


make fs := 'vcons one (plus one) ('vcons 'zero (\ m -> m) 'vnil) : Vec (Nat -> Nat) two ;
make as := 'vcons one two ('vcons 'zero one 'vnil) : Vec Nat two ;
elab vapp Nat Nat two fs as ;




{-
  Another dependent type is the type of finite numbers: |Fin n| is the type of
  natural numbers less than |n|.
-}

idata Fin : Nat -> Set := ('fzero : (n : Nat) -> Fin ('suc n)) ; ('fsuc : (n : Nat) -> Fin n -> Fin ('suc n)) ;

elab 'fzero 'zero              : Fin one ;
elab 'fzero one                : Fin two ;
elab 'fsuc  one ('fzero 'zero) : Fin two ;



{-
  We can prove that, if you have an element of Fin 'zero, you must be lying:
-}

let nuffin (x : Fin 'zero) : :- FF ;
refine nuffin x <= Fin.Ind 'zero x ;
root ;



{-
  Now that we can represent numbers less than a certain value, we can explain
  how to safely lookup an index in a vector. At runtime, it would not be
  necessary to check array bounds, because out-of-bounds accesses are prevented
  by the type system.
-}

let lookup (A : Set)(n : Nat)(as : Vec A n)(fn : Fin n) : A ;
refine lookup A n as fn <= Vec.Ind A n as ;
refine lookup A 'zero 'vnil fn = naughtE (nuffin fn) A	 ;
refine lookup A ('suc k) ('vcons k a as) fn <= Fin.Ind ('suc k) fn ;
refine lookup A ('suc k) ('vcons k a _) ('fzero k) = a ;
refine lookup A ('suc k) ('vcons k a as) ('fsuc k fn) = lookup A k as fn ;
root ;


elab lookup Bool one ('vcons 'zero 'true 'vnil) ('fzero 'zero) ;
elab lookup Bool two ('vcons one 'true ('vcons 'zero 'false 'vnil)) ('fzero one) ;
elab lookup Bool two ('vcons one 'true ('vcons 'zero 'false 'vnil)) ('fsuc one ('fzero 'zero)) ;



{-
  Here ends the demo. If you are feeling brave, go ahead and look at Cat.pig ;-)
-}