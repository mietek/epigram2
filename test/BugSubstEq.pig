data Test := ('A : Set -> Test) ; ('B : Set -> Test) ;

let bug (E : Set)(P : Test -> Set)
    	(pf-AB : :- (: Set) (P ('B E)) == (: Set) (P ('A E)))
	(method : (S : Set) -> P ('B S)) : P ('A E);
-- This solves the problem:
-- = substEq Set (P ('B E)) (P ('A E)) pf-AB (\ x -> x) (method E) ; 
-- This just re-create a new problem, exactly the same:
<= substEq Set (P ('B E)) (P ('A E)) pf-AB ;
