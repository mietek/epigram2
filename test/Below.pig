make DescInd := induction DescD : (v : Desc)(P : Desc -> Set)(p : (x : desc DescD Desc) -> box DescD Desc P x -> P (con x)) -> P v ;

let Below (D : Desc)(Q : Mu D -> Set)(x : Mu D) : Set ;
<= induction D x ;

let BH (X : Desc)(ys : desc X (Mu D))(r : box X (Mu D) P ys) : Set ;
prev ;
define Below D Q _ := BH D x xf ;
next ;

<= DescInd X ;
define BH _ _ _ _ _ _ 'idD ys r := Sig (Below D Q ys ; Q ys) ;
define BH _ _ _ _ _ _ ('constD _) ys [] := Sig () ;
define BH _ _ _ _ _ _ ('sumD e t) [c , ys] r := BH (t c) ys r ;
define BH _ _ _ _ _ _ ('prodD a b) [c , ys] [r1 , r2] := Sig (BH a c r1 ; BH b ys r2) ;
define BH _ _ _ _ _ _ ('sigmaD e t) [c , ys] r := BH (t c) ys r ;
define BH _ _ _ _ _ _ ('piD S T) ys r := (s : S) -> BH (T s) (ys s) (r s) ;
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