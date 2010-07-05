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

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data Vec (A : Set) : Nat -> Set where
   vnil : Vec A ze
   vcons : {n : Nat} -> A -> Vec A n -> Vec A (su n)

data Fin : Nat -> Set where
  fze : {n : Nat} -> Fin (su n)
  fsu : {n : Nat} -> Fin n -> Fin (su n)

data Comp : Set where
  LT : Comp
  EQ : Comp
  GT : Comp

comp : {n : Nat} -> Fin n -> Fin n -> Comp
comp fze fze = EQ
comp fze _ = LT
comp _ fze = GT
comp (fsu n) (fsu n') = comp n n'


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

-- Context and context lookup 
Context : Nat -> Set
Context n = Vec (Sigma Type (\ty -> IMu closeTerm ty)) n

typeAt : {n : Nat}(c : Context n) -> Fin n -> Type
typeAt {ze} c ()
typeAt {su _} (vcons x _) fze = fst x
typeAt {su _} (vcons _ xs) (fsu y) = typeAt xs y

lookup : {n : Nat}(c : Context n)(i : Fin n) -> IMu closeTerm (typeAt c i)
lookup {ze} c ()
lookup {su _} (vcons x _) fze = snd x
lookup {su _} (vcons _ xs) (fsu y) = lookup xs y

-- A variable is an index into the context *and* a proof that the
-- context contains the expected stuff
Var : Nat -> Type -> Set
Var n ty = Fin n

-- Open term: holes are either values or variables in a context
openTerm : Nat -> Type -> IDesc Type
openTerm n = toIDesc Type (exprFree ** (\ty -> Val ty + Var n ty))

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

mergeVars : {n : Nat} ->
            Maybe (List (Fin n * Type)) ->
            Maybe (List (Fin n * Type)) ->
            Maybe (List (Fin n * Type))
mergeVars Nothing _ = Nothing
mergeVars _ Nothing = Nothing
mergeVars (Just []) (Just y) = Just y
mergeVars (Just x) (Just []) = Just x
mergeVars (Just (x :: xs)) (Just (y :: ys)) with comp (fst x) (fst y) 
                                              | mergeVars (Just xs) (Just (y :: ys)) 
                                              | mergeVars (Just (x :: xs)) (Just ys)
... | LT | _        | Nothing   = Nothing
... | LT | _        | Just xys  = Just (y :: xys)
... | EQ | _        | _         = Nothing
... | GT | Nothing  | _         = Nothing
... | GT | Just xys | _         = Just (x :: xys)

collectVars : {ty : Type}{n : Nat} -> IMu (openTerm n) ty -> Maybe (List (Fin n * Type))
collectVars {ty} {n} t = cata Type (openTerm n) (\_ -> Maybe (List (Fin n * Type))) collectVarsHelp ty t
  where collectVarsHelp : (i : Type) -> [| openTerm n i |] (\ _ -> Maybe (List (Fin n * Type))) -> Maybe (List (Fin n * Type))
        collectVarsHelp ty (EZe , r n) = Just ((n , ty) :: [])
        collectVarsHelp ty (EZe , l _) = Just []
        collectVarsHelp ty (ESu EZe , (t1 , ( t2 , t3))) = mergeVars (mergeVars t1 t2) t3
        collectVarsHelp nat (ESu (ESu EZe) , (x , y)) = mergeVars x y
        collectVarsHelp nat (ESu (ESu (ESu ())) , _) 
        collectVarsHelp bool (ESu (ESu EZe) , (x , y) ) = mergeVars x y
        collectVarsHelp bool (ESu (ESu (ESu ())) , _) 
        collectVarsHelp (pair x y) (ESu (ESu ()) , _)
        

ValidContext : {ty : Type}{n : Nat}(c : Context n)(tm : IMu (openTerm n) ty) -> Set
ValidContext {ty} {n} c tm  with collectVars tm
... | Nothing = Zero
... | (Just y) = checkContext y
  where checkContext : List (Fin n * Type) -> Set
        checkContext [] = Unit
        checkContext ((x , ty) :: xs) = ((typeAt c x) == ty) * checkContext xs 

--********************************
-- Evaluation of open terms
--********************************

-- |discharge| is the local substitution expected by |substI|. It is
-- just sugar around context lookup, taking care of transmitting the
-- proof
discharge : {n : Nat}
            {context : Context n}
            (ty : Type) ->
            (Val ty + Var n ty) ->
            IMu closeTerm ty
discharge ty (l value) = con (EZe , value)
discharge {n} {c} ty (r variable) = {!lookup c variable!}
--          (lookup c (fst variable))

-- |substExpr| is the specialized |substI| to expressions. We get it
-- generically from the free monad construction.
substExpr : {n : Nat}
            {ty : Type}
            (context : Context n)
            (sigma : (ty : Type) ->
                     (Val ty + Var n ty) ->
                     IMu closeTerm ty) ->
            (tm : IMu (openTerm n) ty) ->
            ValidContext context tm ->
            IMu closeTerm ty
substExpr {n} {ty} c sig term valid = 
    substI (\ty -> Val ty + Var n ty) Val exprFree sig ty term



{-

-- By first doing substitution to close the term, we can use
-- evaluation of closed terms, obtaining evaluation of open terms
-- under a valid context.
evalOpen : {n : Nat}{ty : Type}
           (context : Context n) ->
           IMu (openTerm context) ty ->
           Val ty
evalOpen context tm = eval (substExpr context discharge tm)

--********************************
-- Tests
--********************************

-- V 0 :-> true, V 1 :-> 2, V 2 :-> ( false , 1 )
testContext : Context _
testContext =  vcons (bool , con (EZe , true )) 
              (vcons (nat , con (EZe , su (su ze)) ) 
              (vcons (pair bool nat , con (EZe , ( false , su ze )))
               vnil))

-- V 1
test1 : IMu (openTerm testContext) nat
test1 = con (EZe , r ( fsu fze , refl ) )

testSubst1 : IMu closeTerm nat
testSubst1 = substExpr testContext 
                       discharge 
                       test1
-- = 2
testEval1 : Val nat
testEval1 = evalOpen testContext test1

-- add 1 (V 1)
test2 : IMu (openTerm testContext) nat
test2 = con (ESu (ESu EZe) , (con (EZe , l (su ze)) , con ( EZe , r (fsu fze , refl) )) )

testSubst2 : IMu closeTerm nat
testSubst2 = substExpr testContext 
                        discharge 
                        test2

-- = 3
testEval2 : Val nat
testEval2 = evalOpen testContext test2

-- if (V 0) then (V 1) else 0
test3 : IMu (openTerm testContext) nat
test3 = con (ESu EZe , (con (EZe , r (fze , refl)) ,
                       (con (EZe , r (fsu fze , refl)) ,
                        con (EZe , l ze))))

testSubst3 : IMu closeTerm nat
testSubst3 = substExpr testContext 
                       discharge 
                       test3

-- = 2
testEval3 : Val nat
testEval3 = evalOpen testContext test3

-- V 2
test4 : IMu (openTerm testContext) (pair bool nat)
test4 = con (EZe , r ( fsu (fsu fze) , refl ) )

testSubst4 : IMu closeTerm (pair bool nat)
testSubst4 = substExpr testContext 
                       discharge 
                       test4
-- = (false , 1)
testEval4 : Val (pair bool nat)
testEval4 = evalOpen testContext test4
-}