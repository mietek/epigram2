make DescInd := induction DescD : (v : Desc)(P : Desc -> Set)(p : (x : desc DescD Desc) -> box DescD Desc P x -> P (con x)) -> P v ;

let Below (D : Desc)(Q : Mu D -> Set)(x : Mu D) : Set ;
<= [x] induction D x ;

let BH (X : Desc)(ys : desc X (Mu D))(r : box X (Mu D) P ys) : Set ;
prev ;
= BH D x xf ;

elim [X] DescInd X ;
give con [? ? ? ? ? ?] ;

simplify ;
= Sig (Below D Q ys ; Q ys) ;

simplify ;
= Sig () ;

give con \ e -> con \ b -> con con con \ t ys r -> ? ;
-- This recursive call is not available because of the broken definition of SUMD
-- (see issue 9).
-- = BH (switchD e b t) ys r ;
next ;

simplify ;
= Sig (BH xf^5 xf^1 xf ; BH xf^4 ys r) ;

simplify ;
= BH./ (xf^1 s) ys r (xf s ys r) ;

simplify ;
= (s : s^2) -> BH./ (xf^1 s) (ys s) (r s) (xf s (ys s) (r s)) ;



root ;


make K    := 'constD (Sig ()) : Desc ;
make NatD := 'sigmaD (Enum ['zero 'suc]) [ K ('prodD 'idD K)] : Desc ;
make Nat  := Mu NatD : Set ;

elab Below NatD ?Q 'zero ; 
elab Below NatD ?Q ('suc 'zero) ;
elab Below NatD ?Q ('suc ('suc 'zero)) ;
elab Below NatD ?Q ('suc ('suc ('suc 'zero))) ;

make TreeD := 'sigmaD (Enum ['leaf 'node]) [ ('prodD ('constD Nat) K) ('prodD 'idD ('prodD 'idD K)) ] : Desc ;
elab Below TreeD ?Q ('node ('leaf 'zero) ('node ('leaf ('suc 'zero)) ('leaf ('suc ('suc 'zero))))) ;