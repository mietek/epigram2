-- The interesting thing is that |node| has two sub-trees, so
-- |induction| can (should be able to) go both left and right.

data Tree := (Leaf : Tree) 
     	   ; (node : Tree -> Tree -> Tree)
	   ;


let traversal (t : Tree) : Tree;
<= Tree.Ind t;
= t;
-- You can go "right":
= traversal xf^2 ;
-- But you cannot go "left":
undo ;
= traversal xf^3 ;
-- Cf. constraint arising at this point