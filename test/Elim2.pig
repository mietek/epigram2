make N := ? : Set ;
make zero := ? : N ;
make suc := ? : N -> N ;

make N-induction := ? : (n : N)(P : N -> Set) -> 
                        P zero -> 
                        ((k : N) -> P k -> P (suc k)) ->
			P n ;

make plus : N -> N -> N;
lambda x ;
elim N-induction x ;
give \ n -> n ;
give \ _ ih y -> suc (ih y) ;

