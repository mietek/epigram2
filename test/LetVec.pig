data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;
make zero := 'zero : Nat ;
make suc := (\ x -> 'suc x) : Nat -> Nat ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus xf^1 n) ;
root ;


module Vec ;
lambda A : Set ;

make VecD : Nat -> IDesc Nat ;
give (\ n -> 'fsigmaD ['nil 'cons] [ ('constD (:- (zero == n))) ('sigmaD Nat (\ m -> 'prodD ('constD A) ('prodD ('varD m) ('constD (:- (suc m == n)))))) ]) ;

make Vec : Nat -> Set ;
lambda n ;
give IMu Nat VecD n ;

make nil := 'nil : Vec 'zero ;
make cons := (\ n a as -> 'cons n a as) : (n : Nat) -> A -> Vec n -> Vec ('suc n) ;

make VecInd := iinduction Nat VecD : (m : Nat)(v : Vec m)
    (bp : Sig (n : Nat ; Vec n) -> Set)
    (me : (k : Nat)(x : idesc Nat (VecD k) Vec)
        (hs : idesc (Sig (i : Nat ; Vec i))
	    (ibox Nat (VecD k) Vec x) bp)
	-> bp [k , con x])
    -> bp [m , v] ;

let vappend (m : Nat)(as : Vec m)(n : Nat)(bs : Vec n) : Vec (plus m n) ;
<= VecInd m as ;
= bs ;
= cons (plus s n) xf^2 (vappend s xf^1 n bs) ;
root ;

make A := Enum ['a 'b 'c] : Set ;

elab Vec.vappend A 'zero 'nil 'zero 'nil  ;

make vab := 'cons ('suc 'zero) 'a ('cons 'zero 'b 'nil) : Vec.Vec A ('suc ('suc 'zero)) ;
elab vab ;
elab Vec.vappend A ('suc ('suc 'zero)) vab ('suc ('suc 'zero)) vab ;

let vtail (A : Set)(n : Nat)(as : Vec.Vec A ('suc n)) : Vec.Vec A n ;
<= Vec.VecInd A ('suc n) as ;
= xf^9 ;
root ;

elab vtail A ('suc 'zero) vab ;