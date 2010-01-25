make N := ? : Set ;
make zero := ? : N ;
make suc := ? : N -> N ;

make Fin := ? : (n : N) -> Set ;
make f0 := ? : (n : N) -> Fin (suc n) ;
make fs := ? : (n : N)(x : Fin n) -> Fin (suc n) ;

make fin-elim := ? : (n : N)
                     (x : Fin n) 
                     (P : (n : N) -> Fin n -> Set) ->
		     ((k : N) -> P (suc k) (f0 k)) ->
		     ((k : N)(y : Fin k) -> P k y -> P (suc k) (fs k y)) ->
		     P n x ;

make T := ? : Fin (suc zero) -> Set ;
make goal : (x : Fin (suc zero)) -> T x ;

lambda x ;
elim fin-elim (suc zero) x ;
show state ;
next ;
show state ;