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

-- Leave plus unimplemented for now, so we can see what we are doing in vappend.
make plus := ? : (m : Nat)(n : Nat) -> Nat ;

{-
let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
= n ;
= 'suc (plus xf^1 n) ;
root ;
-}

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
-- We are left with a couple of equations in the context, so proceeding is hard.

{-
= bs ;
lambda s1, s2, q ;
<= ship Nat s1 s2 _ ;
lambda s1, s2, q, x1, x2, q ;
<= ship Nat s1 s2 _ ;
<= ship Nat 'zero m _ ;
<= ship Nat k m (con (xf % !)) ;
simplify ;
-}

{-
make vappend := (\ m as -> iinduction Nat Vec.VecD m as (\ mas -> (n : Nat) -> Vec n -> Vec (plus (mas !) n)) (\ m -> con [ (\ p _ n as -> ship Nat 'zero m p (\ mm -> Vec (plus mm n)) as) (con \ mm -> con \ a -> con \ as p -> con \ appp _ n as -> ship Nat ('suc mm) m p (\ mmm -> Vec (plus  mmm n)) (vcons (plus mm n) a (appp n as))) ])) : (m : Nat) -> Vec m -> (n : Nat) -> Vec n -> Vec (plus m n) ;
root ;
make ex := Vec.vcons Nat ('suc 'zero) 'zero (Vec.vcons Nat 'zero ('suc 'zero) (Vec.vnil Nat)) : Vec.Vec Nat ('suc ('suc 'zero)) ;
elab ex ;
-}