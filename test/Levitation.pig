-- In the universe of Descriptions

data Nat := ('zero : Nat) 
     	  ; ('suc  : Nat -> Nat) ;

data List (X : Set) := ('nil : List X)
                     ; ('cons : X -> List X -> List X) ;

data Tree (X : Set) := ('leaf : Tree X)
     	       	     ; ('node : Tree X -> X -> Tree X -> Tree X);


let TagDesc : Set ;
= Sig ( E : EnumU ; branches E (\ _ -> Desc) );
root;

let deTag (T : TagDesc) : Desc;
refine deTag [E , T] = 'sigmaD (Enum E) (\ e -> switch E e (\ _ -> Desc) T) ;
root;

let case (D : Desc)(v : Mu D)(P : Mu D -> Set)(p : (x : desc D (Mu D)) -> P (con x)) : P v ;
<= induction D v ;
= p x ;
root;

let replace (D : Desc)(X : Set)(Y : Set)(xs : desc D X)
    	    (hs : box D X (\ _ -> Y) xs) : desc D Y ;
<= induction DescD D ;
refine replace 'idD X Y xs hs = hs ;
refine replace ('constD K) X Y k [] = k ;
refine replace ('sumD E T) X Y [c , d] dd = [ c , replace (T c) X Y d dd ] ;
-- Bug?
--refine replace ('prodD u C D) X Y [c , d] [cc , dd] = [ replace C X Y c cc , replace D X Y d dd ];
refine replace ('prodD u C D) X Y [c , d] [cc , dd] = [ ? , ? ];
= (replace C^1 X^1 Y^1 x xh) call;
= (replace D^1 X^1 Y^1 xs hs) call;
refine replace ('sigmaD S T) X Y [s , d] hs = [ s , replace (T s) X Y d hs ];
refine replace ('piD S T) X Y f g = \ s -> replace (T s) X Y (f s) (g s) ;
root;

let cata (D : Desc)(T : Set)(x : Mu D)(f : desc D T -> T) : T ;
refine cata D T x f = induction D x (\ _ -> T) (\ x -> \ hs -> f (replace D (Mu D) T x hs));
root;

let FreeMonad (T : TagDesc)(X : Set) : TagDesc;
refine FreeMonad [ E , B ] X = [ [ 'var , E ] , [ ('constD X) B ] ];
root;

let Mu+ (D : TagDesc) : Set ;
-- Grr: stop that sigma splitter!
refine Mu+ [E , B] = Mu (deTag [E , B]);
root;

{-
let FMapply (D : TagDesc)(X : Set)(Y : Set)(sigma : X -> Mu+ (FreeMonad D Y))
    	    (x : Mu+ (FreeMonad D X)) : Mu+ (FreeMonad D Y);
<= case (deTag (FreeMonad D X)) x;
-}