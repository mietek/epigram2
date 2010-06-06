module Test;

lambda A : Set;

let test : Set;
-- there is an "A" coming from above
define test A := Sig ();
-- we probably want it to be hidden