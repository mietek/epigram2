let one (X : Set)(f : X -> Enum ['a])(A : :- ((p : X) => f p == (: Enum ['a]) 0 )) : Set;
validate;
root;

let two (Q : Prop)(X : Set)(f : X -> Enum ['a])(A : :- (Q => (p : X) => f p == (: Enum ['a]) 0 )) : Set;
validate;
root;