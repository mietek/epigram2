data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat) ;
make zero := 'zero : Nat ;
make suc := (\ x -> 'suc x) : Nat -> Nat ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus n^1 n) ;
root ;


module Vec ;
lambda A : Set ;

make VecD : Nat -> IDesc Nat ;
give (\ n -> 'fsigmaD ['nil 'cons] [ ('constD (:- (zero == n))) ('sigmaD Nat (\ m -> 'prodD 'a ('constD A) ('prodD 'as ('varD m) ('constD (:- (suc m == n)))))) ]) ;

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
define vappend 'zero 'nil k bs := bs ;
define vappend ('suc s) ('cons s a as) k bs := cons (plus s k) a (vappend s as k bs) ;
root ;

make A := Enum ['a 'b 'c] : Set ;

elab Vec.vappend A 'zero 'nil 'zero 'nil  ;

make vab := 'cons ('suc 'zero) 'a ('cons 'zero 'b 'nil) : Vec.Vec A ('suc ('suc 'zero)) ;
elab vab ;
elab Vec.vappend A ('suc ('suc 'zero)) vab ('suc ('suc 'zero)) vab ;

let vtail (A : Set)(n : Nat)(as : Vec.Vec A ('suc n)) : Vec.Vec A n ;
<= Vec.VecInd A ('suc n) as ;
define vtail A s ('cons s a as) := as ;
root ;

elab vtail A ('suc 'zero) vab ;