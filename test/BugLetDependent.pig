-- Go through:
make NoBug : (X : Set)(f : X -> Enum ['a])(A : :- ((p : X) => f p == (: Enum ['a]) 0 )) -> Set;
validate;
undo;

-- Hung Epigram:
--let Bug (X : Set)(f : X -> Enum ['a])(A : :- ((p : X) => f p == (: Enum ['a]) 0 )) : Set;

-- Hung Epigram:
make NoBug : (X : Set)(f : X -> Enum ['a])(A : :- ((p : X) => f p == (: Enum ['a]) 0 )) -> Set;
lambda X, f;
simpl;