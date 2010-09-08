-- The generic case analysis principle is easy to obtain by ignoring the
-- inductive hypotheses.
make case := (\ D v P p -> induction D v P (\ x _ -> p x)) : (D : Desc)(v : Mu D)(P : Mu D -> Set)(p : (x : desc D (Mu D)) -> P (con x)) -> P v ;

make DescCase := case DescD : (v : Desc)(P : Desc -> Set)(p : (x : desc DescD Desc) -> P (con x)) -> P v ;


-- Now we can write the (moderately useless) generic program that removes a
-- top-level finite sum and replaces it with a sigma.
let f (D : Desc) : Desc ;
<= DescCase D ;
define f 'idD := 'idD ;
define f ('constD K) := 'constD K ;
define f ('sumD e b) := 'sigmaD (Enum e) b ;
define f ('prodD u D E) := 'prodD u D E ;
define f ('sigmaD S T) := 'sigmaD S T ;
define f ('piD S T) := 'piD S T ;
root ;
elab f ('sumD ['zero 'suc] [('constD (Sig ())) 'idD]) ;
