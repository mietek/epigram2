make N := ? : Set ;
make zero := ? : N ;
make suc := ? : N -> N ;

make N-induction := ? : (n : N)(P : N -> Set) -> 
                        P zero -> 
                        ((k : N) -> P k -> P (suc k)) ->
			P n ;

make plus : N -> N -> N;
lambda x ;
elim x N-induction x ;
give \ _ -> x ;
give \ _ ih y -> suc (ih y) ;

