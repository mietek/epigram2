-- Let us start with a substitution axiom:
make substitute := ? : (X : Set)(t : X)(x : X)(P : X -> Set) -> P t -> P x ;

-- Now, we would like to replace x by t in T here:
make goal : (X : Set)(t : X)(T : X -> Set)(x : X) -> T x ;

-- Introduce external hypotheses first:
lambda X;
lambda t;
lambda T;

-- Introduce internal hypothesis next:
lambda x;

-- Apply elim, with the internal context starting at x:
elim substitute X t x ;

show state;

{-

The following, which is tempting, will not work:

make X := ? : Set ;
make t := ? : X ;
make T := ? : X -> Set ;
make e := ? : (x : X)(P : X -> Set) -> P t -> P x ;
make x := ? : X ;
make a : T x ;
elim [x] e x;

Indeed, I deal with the context with getBoys, giving me a list of
references. However, in this case, the context is a bunch of
girls. So, not only will elimination go wrong, but it will not tell
you how bad it feels (producing a disguting motive). I need to find a
solution to that problem.

-}