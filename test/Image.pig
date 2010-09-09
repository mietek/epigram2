load TaggedInduction.pig;

lambda S : Set;
lambda T : Set;
lambda f : S -> T;

idata Im : T -> Set := ('imf : (s : S) -> Im (f s));

let inv (t : T)(y : Im t) : S;
-- ???: rather counter-intuitive to generalize over S, T, and f
refine inv S T f t y <= Im.Case t y;
-- ???: doesn't work (probably because 'f' is re-introduced by EWAM:
-- refine inv S T f (f^1 s) ('imf s) = s;
refine inv S T f _ ('imf s) = s;
root;
