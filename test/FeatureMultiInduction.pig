-- The interesting thing is that |node| has two sub-trees, so
-- |induction| can (should be able to) go both left and right.

data Tree := ('leaf : Tree) 
     	   ; ('node : (tl : Tree) (tr : Tree) -> Tree)
	   ;


let traversal (t : Tree) : Tree;
<= Tree.Ind t;
= 'leaf;
-- You can go "right":
= traversal tl ;
-- But you cannot go "left":
undo ;
= traversal tr ;
-- Cf. constraint arising at this point
give ? ;
-- Should complain, as we should not have a goal left
