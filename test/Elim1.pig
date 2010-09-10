make or := ? : (A : Set)(B : Set) -> Set ;
make or-left := ? : (A : Set)(B : Set)(a : A) -> or A B ;
make or-right := ? : (A : Set)(B : Set)(b : B) -> or A B ;
make or-elim := ? : (A : Set)(B : Set) -> 
                    or A B -> (C : Set) -> (A -> C) -> (B -> C) -> C;
make goal : (P : Set)(Q : Set) -> or P Q -> or Q P ;
lambda P ;
lambda Q ;
lambda PorQ ;
elim or-elim P Q PorQ ;
give \ P Q p _ -> or-right Q P p ;
give \ P Q q _ -> or-left Q P q ;
