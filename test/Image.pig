load TaggedInduction.pig;

lambda S : Set;
lambda T : Set;
lambda f : S -> T;

idata Im : T -> Set := ('imf : (s : S) -> Im (f s));

let inv (t : T)(y : Im t) : S;
refine inv t y <= Im.Case t y;
refine inv (f s) ('imf s) = s;
root;
