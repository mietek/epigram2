make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;


data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

make NatCase : (n : Nat)(P : Nat -> Set)(p : (x : desc Nat.DataDesc Nat) -> P (con x)) -> P n ;
lambda n, P, p ;
give Nat.Ind n P (\ x _ -> p x) ;
root ;

let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus xf^1 n) ;
root ;

module Vec ;
lambda A : Set ;
make Vec : Nat -> Set ;
make VecD := (\ n -> IArg (Enum ['nil 'cons]) [ (IDone ((: Nat) 'zero == n)) (IArg Nat (\ m -> IArg A (\ a -> IInd1 m (IDone ((: Nat) ('suc m) == n))))) ]) : Nat -> IDesc Nat ;

lambda n ;
give IMu Nat VecD n ;

make vnil := con ['nil , _ ] : Vec 'zero ;
make vcons := (\ n a as -> con ['cons n a as , _ ]) : (n : Nat) -> A -> Vec n -> Vec ('suc n) ;

make VecInd := iinduction Nat Vec.VecD : (m : Nat)(v : Vec m)
    (bp : Sig (n : Nat ; Vec n) -> Set)
    (me : (k : Nat)(x : idesc Nat (Vec.VecD k) Vec)
        (hs : idesc (Sig (i : Nat ; Vec i))
	    (ibox Nat (Vec.VecD k) Vec x) bp)
	-> bp [k , con x])
    -> bp [m , v] ;

let vappend (m : Nat)(as : Vec m)(n : Nat)(bs : Vec n) : Vec (plus m n) ;
<= [m] VecInd m as ;

<= ship Nat 'zero k x ;
= bs ;

<= ship Nat ('suc a^1) k x ;
= con ['cons (plus a^2 n) a (vappend a^2 xf^1 n bs) , _ ] ;

root ;


make A := ? : Set ;

{-
make a := ? : A ;
make b := ? : A ;
make c := ? : A ;
make vab := Vec.vcons A ('suc 'zero) a (Vec.vcons A 'zero b (Vec.vnil A)) : Vec.Vec A ('suc ('suc 'zero)) ;
elab vab ;
-}

elab Vec.vappend A 'zero (Vec.vnil A) 'zero (Vec.vnil A) % ! ;