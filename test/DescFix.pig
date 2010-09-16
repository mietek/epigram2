make DescInd := induction DescD : (v : Desc)(P : Desc -> Set)
     (p : (x : desc DescD Desc) -> box DescD Desc P x -> P (con x)) -> P v ;

let BH (D : Desc)(Q : Mu D -> Set)(X : Desc)(ys : desc X (Mu D))
    (r : box X (Mu D) (\ a -> ((Q : Mu D -> Set) -> Set)) ys) : Set ;
refine BH D Q X ys r <= DescInd X ;
refine BH D Q 'idD ys r = Sig (r Q ; Q ys) ;
refine BH D Q ('constD c) ys [] = Sig () ;
refine BH D Q ('sumD S T) [c , ys] r = BH D Q (T c) ys r ;
refine BH D Q ('prodD u S T) [ysS , ysT] [rS , rT] = Sig (BH D Q S ysS rS ; BH D Q T ysT rT) ;
refine BH D Q ('sigmaD S T) [s , ys] r = BH D Q (T s) ys r ;
refine BH D Q ('piD S T) ys r = (s : S) -> BH D Q (T s) (ys s) (r s) ;
root ;

make Below : (D : Desc)(Q : Mu D -> Set)(x : Mu D) -> Set ;
lambda D, Q, x ;
elim induction D x ;
lambda D, x, r, Q ;
give BH D Q D x r ;
root ;


make K    := 'constD (Sig ()) : Desc ;
make NatD := 'sigmaD (Enum ['zero 'suc]) [ K ('prodD 'n 'idD K)] : Desc ;
make Nat  := Mu NatD : Set ;

elab Below NatD ?Q 'zero ; 
elab Below NatD ?Q ('suc 'zero) ;
elab Below NatD ?Q ('suc ('suc 'zero)) ;
elab Below NatD ?Q ('suc ('suc ('suc 'zero))) ;

make TreeD := 'sigmaD (Enum ['leaf 'node]) [ ('prodD 'n ('constD Nat) K) ('prodD 'tl 'idD ('prodD 'tr 'idD K)) ] : Desc ;
elab Below TreeD ?Q ('node ('leaf 'zero) ('node ('leaf ('suc 'zero)) ('leaf ('suc ('suc 'zero))))) ;



let genHelp (D : Desc)
       	    (Q : Mu D -> Set)
	    (body : (x : Mu D)(below : Below D Q x) -> Q x)
       	    (X : Desc)
       	    (ys : desc X (Mu D))
       	    (r : box X (Mu D)
	      (\ a -> ((Q : Mu D -> Set)(body : (x : Mu D)
	                   (below : Below D Q x) -> Q x) -> Below D Q a)) ys)
       	    : BH D Q X ys
	        (mapBox X (Mu D) (\ a -> ((Q : Mu D -> Set) -> Set)) 
		    (\ x Q -> Below D Q x) ys) ;
refine genHelp D Q body X ys r <= DescInd X ;

-- For some reason, this does not work as a single step
= [? , ?] ;
give r Q body ;
give body ys (r Q body) ;

refine genHelp D Q body ('sumD E T) [e , ys] r = genHelp D Q body (T e) ys r ;

relabel genHelp D Q body ('prodD u A B) [ysA , ysB] [rA , rB] ;
= [? , ?] ;
give genHelp D Q body A ysA rA ;
give genHelp D Q body B ysB rB ;

refine genHelp D Q body ('sigmaD S T) [s , ys] r = genHelp D Q body (T s) ys r;
refine genHelp D Q body ('piD S T) ys r = \ s -> genHelp D Q body (T s) (ys s) (r s) ;
root ;

make gen : (D : Desc)
           (Q : Mu D -> Set)
	   (body : (x : Mu D)(below : Below D Q x) -> Q x)
	   (x : Mu D)
	   -> Below D Q x ;
lambda D, Q, body, x ;
elim induction D x ;
lambda D, x, r, Q, body ;
give genHelp D Q body D x r ;
root ;


let Fix (D : Desc)(x : Mu D)(Q : Mu D -> Set)(m : (x : Mu D) -> Below D Q x -> Q x) : Q x ;
refine Fix D x Q m = m x (gen D Q m x) ;
root ;



data Nat := ('zero : Nat) ; ('suc : Nat -> Nat) ;
make NatCase : (n : Nat)(P : (n : Nat) -> Set)(p : (nt : desc Nat.DataDesc Nat) -> P (con nt)) -> P n ;
lambda n, P, p ;
give Nat.Ind n P (\ x _ -> p x) ;
root ;

make NatFix := Fix Nat.DataDesc : (x : Nat)(Q : Nat -> Set)(m : (x : Nat) -> Below Nat.DataDesc Q x -> Q x) -> Q x ;

let plus (m : Nat)(n : Nat) : Nat ;
refine plus m n <= NatFix m ;
refine plus m n <= NatCase m ;
refine plus 'zero n = n ;
refine plus ('suc k) n = 'suc (plus k n) ;
root ;

let fib (n : Nat) : Nat ;
refine fib n <= NatFix n ;
refine fib n <= NatCase n ;
refine fib 'zero = 'suc 'zero ;
refine fib ('suc m) <= NatCase m ;
refine fib ('suc 'zero) = 'suc 'zero ;
refine fib ('suc ('suc k)) = plus (fib k) (fib ('suc k)) ;
root ;

