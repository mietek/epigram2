-- To help see where we are going, let's specialise the generic induction
-- principle to Desc itself.
make DescInd := induction DescD : (v : Desc)(P : Desc -> Set)(p : (x : desc DescD Desc) -> box DescD Desc P x -> P (con x)) -> P v ;

-- Now we can calculate the derivative of a description...
let delta (D : Desc) : Desc ;
<= DescInd D ;

-- The derivative of X is 1:
define delta 'idD := 'constD (Sig ()) ;

-- The deriviative of a constant is 0:
define delta ('constD _) := 'constD (:- FF) ;

-- Enumerations are just finite sums, so differentiation is linear:
define delta ('sumD e b) := 'sumD e (\ x -> delta (b x)) ;

-- Everyone loves the product rule:
define delta ('prodD u D1 D2) := 'sigmaD (Enum ['left 'right]) [('prodD 'l (delta D1) D2) ('prodD 'r D1 (delta D2))] ;

-- Differentation is linear over sums:
define delta ('sigmaD S T) := 'sigmaD S (\ s -> delta (T s)) ;

-- To differentiate a big product, pick a position for the hole,
-- differentiate there and multiply by the other positions:
define delta ('piD S T) := 'sigmaD S (\ s -> 'prodD 'h (delta (T s)) ('piD (Sig (a : S ; :- (s == a => FF))) (\ v -> T (v !)))) ;
-- Is this right? Can we encode it more nicely?

root ;


-- Let's try it out!

-- The constant functor has zero deriviative:
make K    := 'constD (Sig ()) : Desc ;
elab delta K ;

-- The derivative of 1 + X is 1:
make NatD := 'sigmaD (Enum ['zero 'suc]) [ K ('prodD 'n 'idD K)] : Desc ;
elab 'suc 'left _ : Mu (delta NatD) ;

-- Let D be the description of 1 + X + X^2
make D := 'sigmaD (Enum ['a 'b 'c]) [K 'idD ('prodD 'l 'idD 'idD)] : Desc ;
-- then D differentiates to give 1 + 2X:
elab con ['b , _ ] : Mu (delta D) ;
elab con ['c , ['left  , [_  , 'b]]] : Mu (delta D) ;
elab con ['c , ['right , ['b ,  _]]] : Mu (delta D) ;
