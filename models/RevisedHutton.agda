 {-# OPTIONS --type-in-type #-}

module RevisedHutton where

--********************************************
-- Prelude
--********************************************

-- Some preliminary stuffs, to avoid relying on the stdlib

--****************
-- Sigma and friends
--****************

data Sigma (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) -> Sigma A B

_*_ : (A : Set)(B : Set) -> Set
A * B = Sigma A \_ -> B

fst : {A : Set}{B : A -> Set} -> Sigma A B -> A
fst (a , _) = a

snd : {A : Set}{B : A -> Set} (p : Sigma A B) -> B (fst p)
snd (a , b) = b

data Zero : Set where
data Unit  : Set where
  Void : Unit

--****************
-- Sum and friends
--****************

data _+_ (A : Set)(B : Set) : Set where
  l : A -> A + B
  r : B -> A + B

--****************
-- Equality
--****************

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

subst : forall {x y} -> x == y -> x -> y
subst refl x = x

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong2 : {A B C : Set}(f : A -> B -> C){x y : A}{z t : B} -> 
        x == y -> z == t -> f x z == f y t
cong2 f refl refl = refl

postulate 
  reflFun : {A B : Set}(f : A -> B)(g : A -> B)-> ((a : A) -> f a == g a) -> f == g 

--****************
-- Meta-language
--****************

-- Note that we could define Nat, Bool, and the related operations in
-- IDesc. But it is awful to code with them, in Agda.

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

plus : Nat -> Nat -> Nat
plus ze n' = n'
plus (su n) n' = su (plus n n')

le : Nat -> Nat -> Bool
le ze _ = true
le (su _) ze = false
le (su n) (su n') = le n n'

data Vec (A : Set) : Nat -> Set where
   vnil : Vec A ze
   vcons : {n : Nat} -> A -> Vec A n -> Vec A (su n)

data Fin : Nat -> Set where
  fze : {n : Nat} -> Fin (su n)
  fsu : {n : Nat} -> Fin n -> Fin (su n)



--********************************************
-- Desc code
--********************************************

data IDesc (I : Set) : Set where
  var : I -> IDesc I
  const : Set -> IDesc I
  prod : IDesc I -> IDesc I -> IDesc I
  sigma : (S : Set) -> (S -> IDesc I) -> IDesc I
  pi : (S : Set) -> (S -> IDesc I) -> IDesc I


--********************************************
-- Desc interpretation
--********************************************

[|_|] : {I : Set} -> IDesc I -> (I -> Set) -> Set
[| var i |] P = P i
[| const X |] P = X
[| prod D D' |] P = [| D |] P * [| D' |] P
[| sigma S T |] P = Sigma S (\s -> [| T s |] P)
[| pi S T |] P = (s : S) -> [| T s |] P

--********************************************
-- Fixpoint construction
--********************************************

data IMu {I : Set}(R : I -> IDesc I)(i : I) : Set where
  con : [| R i |] (\j -> IMu R j) -> IMu R i

--********************************************
-- Predicate: All
--********************************************

All : {I : Set}(D : IDesc I)(P : I -> Set) -> [| D |] P -> IDesc (Sigma I P)
All (var i)     P x        = var (i , x)
All (const X)   P x        = const Unit
All (prod D D') P (d , d') = prod (All D P d) (All D' P d')
All (sigma S T) P (a , b)  = All (T a) P b
All (pi S T)    P f        = pi S (\s -> All (T s) P (f s))

--********************************************
-- Elimination principle: induction
--********************************************

module Elim {I : Set}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : [| R i |] (IMu R))
                 (hs : [| All (R i) (IMu R) xs |] P) ->
                 P ( i , con xs ))
       where

  mutual
    indI : (i : I)(x : IMu R i) -> P (i , x)
    indI i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> 
           (xs : [| D |] (IMu R)) -> 
           [| All D (IMu R) xs |] P
    hyps (var i) x = indI i x
    hyps (const X) x = Void
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


indI : {I : Set}
       (R : I -> IDesc I)
       (P : Sigma I (IMu R) -> Set)
       (m : (i : I)
            (xs : [| R i |] (IMu R))
            (hs : [| All (R i) (IMu R) xs |] P) ->
            P ( i , con xs)) ->
       (i : I)(x : IMu R i) -> P ( i , x )
indI = Elim.indI


--********************************************
-- Enumerations (hard-coded)
--********************************************

-- Unlike in Desc.agda, we don't carry the levitation of finite sets
-- here. We hard-code them and manipulate with standard Agda
-- machinery. Both presentation are isomorph but, in Agda, the coded
-- one quickly gets unusable.

data EnumU : Set where
  nilE : EnumU
  consE : EnumU -> EnumU

data EnumT : (e : EnumU) -> Set where
  EZe : {e : EnumU} -> EnumT (consE e)
  ESu : {e : EnumU} -> EnumT e -> EnumT (consE e)

spi : (e : EnumU)(P : EnumT e -> Set) -> Set
spi nilE P = Unit
spi (consE e) P = P EZe * spi e (\e -> P (ESu e))

switch : (e : EnumU)(P : EnumT e -> Set)(b : spi e P)(x : EnumT e) -> P x
switch nilE P b ()
switch (consE e) P b EZe = fst b
switch (consE e) P b (ESu n) = switch e (\e -> P (ESu e)) (snd b) n

_++_ : EnumU -> EnumU -> EnumU
nilE ++ e' = e'
(consE e) ++ e' = consE (e ++ e')

-- A special switch, for tagged descriptions. Switching on a
-- concatenation of finite sets:
sswitch : (e : EnumU)(e' : EnumU)(P : Set)
       (b : spi e (\_ -> P))(b' : spi e' (\_ -> P))(x : EnumT (e ++ e')) -> P
sswitch nilE nilE P b b' ()
sswitch nilE (consE e') P b b' EZe = fst b'
sswitch nilE (consE e') P b b' (ESu n) = sswitch nilE e' P b (snd b') n
sswitch (consE e) e' P b b' EZe = fst b
sswitch (consE e) e' P b b' (ESu n) = sswitch e e' P (snd b) b' n

--********************************************
-- Tagged indexed description
--********************************************

FixMenu : Set -> Set
FixMenu I = Sigma EnumU (\e -> (i : I) -> spi e (\_ -> IDesc I))

SensitiveMenu : Set -> Set
SensitiveMenu I = Sigma (I -> EnumU) (\F -> (i : I) -> spi (F i) (\_ -> IDesc I))

TagIDesc : Set -> Set
TagIDesc I = FixMenu I * SensitiveMenu I

toIDesc : (I : Set) -> TagIDesc I -> (I -> IDesc I)
toIDesc I ((E , ED) , (F , FD)) i = sigma (EnumT (E ++ F i)) 
                                          (\x -> sswitch E (F i) (IDesc I) (ED i) (FD i) x)

--********************************************
-- Catamorphism
--********************************************

cata : (I : Set)
       (R : I -> IDesc I)
       (T : I -> Set) ->
       ((i : I) -> [| R i |] T -> T i) ->
       (i : I) -> IMu R i -> T i
cata I R T phi i x = indI R (\it -> T (fst it)) (\i xs ms -> phi i (replace (R i) T xs ms)) i x
  where replace : (D : IDesc I)(T : I -> Set)
                  (xs : [| D |] (IMu R))
                  (ms : [| All D (IMu R) xs |] (\it -> T (fst it))) -> 
                  [| D |] T
        replace (var i) T x y = y
        replace (const Z) T z z' = z
        replace (prod D D') T (x , x') (y , y') = replace D T x y , replace D' T x' y'
        replace (sigma A B) T (a , b) t = a , replace (B a) T b t
        replace (pi A B) T f t = \s -> replace (B s) T (f s) (t s)

--********************************************
-- Hutton's razor
--********************************************

--********************************
-- Types code
--********************************

data Type : Set where
  nat : Type
  bool : Type
  pair : Type -> Type -> Type


--********************************************
-- Free monad construction
--********************************************

_**_ : {I : Set} (R : TagIDesc I)(X : I -> Set) -> TagIDesc I
((E , ED) , FFD) ** X = ((( consE E ,  \ i -> ( const (X i) , ED i ))) , FFD) 


--********************************************
-- Substitution
--********************************************

apply : {I : Set}
        (R : TagIDesc I)(X Y : I -> Set) ->
        ((i : I) -> X i -> IMu (toIDesc I (R ** Y)) i) ->
        (i : I) -> 
        [| toIDesc I (R ** X) i |] (IMu (toIDesc I (R ** Y))) ->
        IMu (toIDesc I (R ** Y)) i
apply (( E , ED) , (F , FD)) X Y sig i (EZe , x) = sig i x
apply (( E , ED) , (F , FD)) X Y sig i (ESu n , t) = con (ESu n , t)

substI : {I : Set} (X Y : I -> Set)(R : TagIDesc I)
         (sigma : (i : I) -> X i -> IMu (toIDesc I (R ** Y)) i)
         (i : I)(D : IMu (toIDesc I (R ** X)) i) ->
         IMu (toIDesc I (R ** Y)) i
substI {I} X Y R sig i term = cata I (toIDesc I (R ** X)) (IMu (toIDesc I (R ** Y))) (apply R X Y sig) i term 


--********************************************
-- Hutton's razor is free monad
--********************************************

-- Fix menu:
exprFreeFixMenu : FixMenu Type
exprFreeFixMenu = ( consE nilE , 
                    \ty -> (prod (var bool) (prod (var ty) (var ty)), -- if b then t1 else t2
                           Void))

-- Index-dependent menu:
choiceFreeMenu : Type -> EnumU
choiceFreeMenu nat = consE nilE
choiceFreeMenu bool = consE nilE
choiceFreeMenu (pair x y) = nilE

choiceFreeDessert : (ty : Type) -> spi (choiceFreeMenu ty) (\ _ -> IDesc Type)
choiceFreeDessert nat = (prod (var nat) (var nat) , Void)     -- plus x y
choiceFreeDessert bool = (prod (var nat) (var nat) , Void )   -- le x y
choiceFreeDessert (pair x y) = Void

exprFreeSensitiveMenu : SensitiveMenu Type
exprFreeSensitiveMenu = ( choiceFreeMenu ,  choiceFreeDessert )

-- Tagged description of expressions
exprFree : TagIDesc Type
exprFree = exprFreeFixMenu , exprFreeSensitiveMenu

-- Free monadic expressions
exprFreeC : (Type -> Set) -> TagIDesc Type
exprFreeC X = exprFree ** X

--********************************
-- Closed terms
--********************************

Val : Type -> Set
Val nat = Nat
Val bool = Bool
Val (pair x y) = (Val x) * (Val y)

closeTerm : Type -> IDesc Type
closeTerm = toIDesc Type (exprFree ** Val)

--********************************
-- Closed term evaluation
--********************************

eval : {ty : Type} -> IMu closeTerm ty -> Val ty
eval {ty} term = cata Type closeTerm Val evalOneStep ty term
        where evalOneStep : (ty : Type) -> [| closeTerm ty |] Val -> Val ty
              evalOneStep _ (EZe , t) = t
              evalOneStep _ ((ESu EZe) , (true , ( x , _))) = x
              evalOneStep _ ((ESu EZe) , (false , ( _ , y ))) = y
              evalOneStep nat ((ESu (ESu EZe)) , (x , y)) = plus x y
              evalOneStep nat ((ESu (ESu (ESu ()))) , t) 
              evalOneStep bool ((ESu (ESu EZe)) , (x , y) ) =   le x y
              evalOneStep bool ((ESu (ESu (ESu ()))) , _) 
              evalOneStep (pair x y) (ESu (ESu ()) , _)


--********************************
-- [Open terms]
--********************************

-- A context is a snoc-list of types
-- put otherwise, a context is a type telescope
data Context : Set where
  [] : Context
  _,_ : Context -> Type -> Context

-- The environment realizes the context, having a value for each type
Env : Context -> Set
Env []      = Unit
Env (G , S)  = Env G * Val S

-- A typed-variable indexes into the context, obtaining a proof that
-- what we get is what you want (WWGIWYW)
Var : Context -> Type -> Set
Var []      T = Zero
Var (G , S) T = Var G T + (S == T)

-- The lookup gets into the context to extract the value
lookup : (G : Context) -> Env G -> (T : Type) -> Var G T -> Val T
lookup []        _       T ()
lookup (G , .T)  (g , t) T (r refl) = t
lookup (G , S)   (g , t) T (l x)    = lookup G g T x 

-- Open term: holes are either values or variables in a context
openTerm : Context -> Type -> IDesc Type
openTerm c = toIDesc Type (exprFree ** (\ty -> Val ty + Var c ty))

--********************************
-- Evaluation of open terms
--********************************

-- |discharge| is the local substitution expected by |substI|. It is
-- just sugar around context lookup
discharge : (context : Context) ->
            Env context ->
            (ty : Type) ->
            (Val ty + Var context ty) ->
            IMu closeTerm ty
discharge ctxt env ty (l value) = con (EZe , value)
discharge ctxt env ty (r variable) = con (EZe , lookup ctxt env ty variable ) 

-- |substExpr| is the specialized |substI| to expressions. We get it
-- generically from the free monad construction.
substExpr : {ty : Type}
            (context : Context)
            (sigma : (ty : Type) ->
                     (Val ty + Var context ty) ->
                     IMu closeTerm ty) ->
            IMu (openTerm context) ty ->
            IMu closeTerm ty
substExpr {ty} c sig term = 
    substI (\ty -> Val ty + Var c ty) Val exprFree sig ty term

-- By first doing substitution to close the term, we can use
-- evaluation of closed terms, obtaining evaluation of open terms
-- under a valid context.
evalOpen : {ty : Type}(context : Context) ->
           Env context ->
           IMu (openTerm context) ty ->
           Val ty
evalOpen ctxt env tm = eval (substExpr ctxt (discharge ctxt env) tm)

--********************************
-- Tests
--********************************

-- Test context:
-- V 0 :-> true, V 1 :-> 2, V 2 :-> ( false , 1 )
testContext : Context
testContext = (([] , bool) , nat) , pair bool nat
testEnv : Env testContext
testEnv = ((Void , true ) , su (su ze)) , (false , su ze) 

-- V 1
test1 : IMu (openTerm testContext) nat
test1 = con (EZe , r ( l (r refl) ) )

testSubst1 : IMu closeTerm nat
testSubst1 = substExpr testContext 
                       (discharge testContext testEnv)
                       test1
-- = 2
testEval1 : Val nat
testEval1 = evalOpen testContext testEnv test1

-- add 1 (V 1)
test2 : IMu (openTerm testContext) nat
test2 = con (ESu (ESu EZe) , (con (EZe , l (su ze)) , con ( EZe , r (l (r refl)) )) )

testSubst2 : IMu closeTerm nat
testSubst2 = substExpr testContext 
                       (discharge testContext testEnv)
                        test2

-- = 3
testEval2 : Val nat
testEval2 = evalOpen testContext testEnv test2


-- if (V 0) then (V 1) else 0
test3 : IMu (openTerm testContext) nat
test3 = con (ESu EZe , (con (EZe , r (l (l (r refl)))) ,
                       (con (EZe , r (l (r refl))) ,
                        con (EZe , l ze))))

testSubst3 : IMu closeTerm nat
testSubst3 = substExpr testContext 
                       (discharge testContext testEnv)
                       test3

-- = 2
testEval3 : Val nat
testEval3 = evalOpen testContext testEnv test3

-- V 2
test4 : IMu (openTerm testContext) (pair bool nat)
test4 = con (EZe , r ( r refl ) )

testSubst4 : IMu closeTerm (pair bool nat)
testSubst4 = substExpr testContext 
                       (discharge testContext testEnv)
                       test4
-- = (false , 1)
testEval4 : Val (pair bool nat)
testEval4 = evalOpen testContext testEnv test4