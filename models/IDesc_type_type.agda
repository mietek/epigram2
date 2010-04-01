 {-# OPTIONS --type-in-type #-}

module IDesc_type_type where

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

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

cong2 : {A B C : Set}(f : A -> B -> C){x y : A}{z t : B} -> 
        x == y -> z == t -> f x z == f y t
cong2 f refl refl = refl


-- Intensionally extensional
postulate 
  reflFun : {A B : Set}(f : A -> B)(g : A -> B)-> ((a : A) -> f a == g a) -> f == g 

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

desc : {I : Set} -> IDesc I -> (I -> Set) -> Set
desc (var i) P = P i
desc (const X) P = X
desc (prod D D') P = desc D P * desc D' P
desc (sigma S T) P = Sigma S (\s -> desc (T s) P)
desc (pi S T) P = (s : S) -> desc (T s) P

--********************************************
-- Fixpoint construction
--********************************************

data IMu {I : Set}(R : I -> IDesc I)(i : I) : Set where
  con : desc (R i) (\j -> IMu R j) -> IMu R i

--********************************************
-- Predicate: All
--********************************************

All : {I : Set}(D : IDesc I)(P : I -> Set) -> desc D P -> IDesc (Sigma I P)
All (var i)     P x        = var (i , x)
All (const X)   P x        = const X
All (prod D D') P (d , d') = prod (All D P d) (All D' P d')
All (sigma S T) P (a , b)  = All (T a) P b
All (pi S T)    P f        = pi S (\s -> All (T s) P (f s))

all : {I : Set}(D : IDesc I)(X : I -> Set)
      (R : Sigma I X -> Set)(P : (x : Sigma I X) -> R x) -> (xs : desc D X) -> desc (All D X xs) R
all (var i) X R P x = P (i , x)
all (const K) X R P k = k
all (prod D D') X R P (x , y) = ( all D X R P x , all D' X R P y )
all (sigma S T) X R P (a , b) = all (T a) X R P b
all (pi S T) X R P f = \a -> all (T a) X R P (f a)

--********************************************
-- Enumerations (hard-coded)
--********************************************

data EnumU : Set where
  nilE : EnumU
  consE : EnumU -> EnumU

data EnumT : (e : EnumU) -> Set where
  EZe : {e : EnumU} -> EnumT (consE e)
  ESu : {e : EnumU} -> EnumT e -> EnumT (consE e)

_++_ : EnumU -> EnumU -> EnumU
nilE ++ e' = e'
(consE e) ++ e' = consE (e ++ e')

spi : (e : EnumU)(P : EnumT e -> Set) -> Set
spi nilE P = Unit
spi (consE e) P = P EZe * spi e (\e -> P (ESu e))

switch : (e : EnumU)(P : EnumT e -> Set)(b : spi e P)(x : EnumT e) -> P x
switch nilE P b ()
switch (consE e) P b EZe = fst b
switch (consE e) P b (ESu n) = switch e (\e -> P (ESu e)) (snd b) n

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
-- Elimination principle: induction
--********************************************

module Elim {I : Set}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (All (R i) (IMu R) xs) P) ->
                 P ( i , con xs ))
       where

  mutual
    induction : (i : I)(x : IMu R i) -> P (i , x)
    induction i (con xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> 
           (xs : desc D (IMu R)) -> 
           desc (All D (IMu R) xs) P
    hyps (var i) x = induction i x
    hyps (const X) x = x -- ??
    hyps (prod D D') (d , d') =  hyps D d , hyps D' d'
    hyps (pi S R) f = \ s -> hyps (R s) (f s)
    hyps (sigma S R) ( a , b ) = hyps (R a) b


induction : {I : Set}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (All (R i) (IMu R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu R i) -> P ( i , x )
induction = Elim.induction

{-
induction : {I : Set}
            (R : I -> IDesc I)
            (P : Sigma I (IMu R) -> Set)
            (m : (i : I)
                 (xs : desc (R i) (IMu R))
                 (hs : desc (All (R i) (IMu R) xs) P) ->
                 P ( i , con xs)) ->
            (i : I)(x : IMu R i) -> P ( i , x )
induction {I} R P m i (con xs) = m i xs (all (R i) (IMu R) P induct xs)
  where induct : (x : Sigma I (IMu R)) -> P x
        induct (i , xs) = induction R P m i xs
-}

--********************************************
-- DescD
--********************************************

data DescDConst : Set where
  lvar   : DescDConst
  lconst : DescDConst
  lprod  : DescDConst
  lpi    : DescDConst
  lsigma : DescDConst

descDChoice : Set -> DescDConst -> IDesc Unit
descDChoice I lvar = const I
descDChoice _ lconst = const Set
descDChoice _ lprod = prod (var Void) (var Void)
descDChoice _ lpi = sigma Set (\S -> pi S (\s -> var Void))
descDChoice _ lsigma = sigma Set (\S -> pi S (\s -> var Void))

descD : (I : Set) -> IDesc Unit
descD I = sigma DescDConst (descDChoice I)

IDescl0 : (I : Set) -> Unit -> Set
IDescl0 I = IMu (\_ -> descD I) 

IDescl : (I : Set) -> Set
IDescl I = IDescl0 I _

varl : {I : Set}(i : I) -> IDescl I
varl i = con (lvar ,  i)

constl : {I : Set}(X : Set) -> IDescl I
constl X = con (lconst , X)

prodl : {I : Set}(D D' : IDescl I) -> IDescl I
prodl D D' = con (lprod , (D , D'))

pil : {I : Set}(S : Set)(T : S -> IDescl I) -> IDescl I
pil S T = con (lpi , ( S , T))

sigmal : {I : Set}(S : Set)(T : S -> IDescl I) -> IDescl I
sigmal S T = con (lsigma , ( S , T))



--********************************************
-- From the embedding to the host
--********************************************

cases : {I : Set}
        (xs : desc (descD I) (IMu (λ _ -> descD I)))
        (hs : desc (All (descD I) (IMu (λ _ -> descD I)) xs) (λ _ -> IDesc I)) ->
        IDesc I
cases ( lvar , i ) hs =  var i
cases ( lconst , X ) hs =  const X
cases ( lprod , (D , D') ) ( d , d' ) =  prod d d'
cases ( lpi , ( S , T ) ) hs =  pi S hs
cases ( lsigma , ( S , T ) ) hs = sigma S hs

phi : {I : Set} -> IDescl I -> IDesc I
phi {I} d = induction (\_ -> descD I) (\_ -> IDesc I) (\_ -> cases) Void d

--********************************************
-- From the host to the embedding
--********************************************

psi : {I : Set} -> IDesc I -> IDescl I
psi (var i) = varl i
psi (const X) = constl X
psi (prod D D') = prodl (psi D) (psi D')
psi (pi S T) = pil S (\s -> psi (T s))
psi (sigma S T) = sigmal S (\s -> psi (T s))


--********************************************
-- Isomorphism proof
--********************************************

-- From host to host

proof-phi-psi : {I : Set} -> (D : IDesc I) -> phi (psi D) == D
proof-phi-psi (var i) = refl
proof-phi-psi (const x) = refl
proof-phi-psi (prod D D') with proof-phi-psi D | proof-phi-psi D'
...  | p | q = cong2 prod p q
proof-phi-psi (pi S T) = cong (pi S)  
                                (reflFun (\ s -> phi (psi (T s)))
                                         T
                                         (\s -> proof-phi-psi (T s)))
proof-phi-psi (sigma S T) = cong (sigma S) 
                                   (reflFun (\ s -> phi (psi (T s)))
                                            T
                                            (\s -> proof-phi-psi (T s)))


-- From embedding to embedding

proof-psi-phi : (I : Set) -> (D : IDescl I) -> psi (phi D) == D
proof-psi-phi I D =  induction (\ _ -> descD I)
                               P
                               proof-psi-phi-cases
                               Void
                               D
                where P : Sigma Unit (IMu (\ x -> descD I)) -> Set
                      P ( Void , D ) = psi (phi D) == D
                      proof-psi-phi-cases : (i : Unit)
                                            (xs : desc (descD I) (IDescl0 I))
                                            (hs : desc (All (descD I) (IDescl0 I) xs) P)
                                            -> P (i , con xs)
                      proof-psi-phi-cases Void (lvar , i) hs = refl
                      proof-psi-phi-cases Void (lconst , x) hs = refl
                      proof-psi-phi-cases Void (lprod , ( D , D' )) ( p , q ) = cong2 prodl p q 
                      proof-psi-phi-cases Void (lpi , ( S , T )) hs = cong (pil S) 
                                                                           (reflFun (\ s -> psi (phi (T s)))
                                                                                    T
                                                                                    hs)
                      proof-psi-phi-cases Void (lsigma , ( S , T )) hs = cong (sigmal S) 
                                                                              (reflFun (λ s -> psi (phi (T s)))
                                                                                       T
                                                                                       hs)

--********************************************
-- Catamorphism
--********************************************

cata : (I : Set)
       (R : I -> IDesc I)
       (T : I -> Set) ->
       ((i : I) -> desc (R i) T -> T i) ->
       (i : I) -> IMu R i -> T i
cata I R T phi i x = induction R (\it -> T (fst it)) (\i xs ms -> phi i (replace (R i) T xs ms)) i x
  where replace : (D : IDesc I)(T : I -> Set)
                  (xs : desc D (IMu R))
                  (ms : desc (All D (IMu R) xs) (\it -> T (fst it))) -> 
                  desc D T
        replace (var i) T x y = y
        replace (const Z) T z z' = z'
        replace (prod D D') T (x , x') (y , y') = replace D T x y , replace D' T x' y'
        replace (sigma A B) T (a , b) t = a , replace (B a) T b t
        replace (pi A B) T f t = \s -> replace (B s) T (f s) (t s)

--********************************************
-- Hutton's razor
--********************************************

--********************************
-- Meta-language
--********************************

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


--********************************
-- Types code
--********************************

data Type : Set where
  nat : Type
  bool : Type


--********************************
-- Typed expressions
--********************************

exprFixMenu : (Type -> Set) -> FixMenu Type
exprFixMenu constt = ( consE (consE nilE) , 
                       \ty -> (const (constt ty),
                              (prod (var bool) (prod (var ty) (var ty)), 
                               Void)))

choiceMenu : Type -> EnumU
choiceMenu nat = consE nilE
choiceMenu bool = consE nilE

choiceDessert : (ty : Type) -> spi (choiceMenu ty) (\ _ -> IDesc Type)
choiceDessert nat = (prod (var nat) (var nat) , Void)
choiceDessert bool = (prod (var nat) (var nat) , Void )

exprSensitiveMenu : SensitiveMenu Type
exprSensitiveMenu = ( choiceMenu ,  choiceDessert )

expr : (Type -> Set) -> TagIDesc Type
expr constt = exprFixMenu constt , exprSensitiveMenu

exprIDesc : (Type -> Set) -> ((Type -> Set) -> TagIDesc Type) -> (Type -> IDesc Type)
exprIDesc constt D = toIDesc Type  (D constt)


--********************************
-- Closed terms
--********************************

Val : Type -> Set
Val nat = Nat
Val bool = Bool

closeTerm : Type -> IDesc Type
closeTerm = exprIDesc Val expr


--********************************
-- Closed term evaluation
--********************************

eval : (ty : Type) -> IMu closeTerm ty -> Val ty
eval ty term = cata Type closeTerm Val evalOneStep ty term
        where evalOneStep : (ty : Type) -> desc (closeTerm ty) Val -> Val ty
              evalOneStep _ (EZe , t) = t
              evalOneStep _ ((ESu EZe) , (true , ( x , _))) = x
              evalOneStep _ ((ESu EZe) , (false , ( _ , y ))) = y
              evalOneStep nat ((ESu (ESu EZe)) , (x , y)) = plus x y
              evalOneStep nat ((ESu (ESu (ESu ()))) , t) 
              evalOneStep bool ((ESu (ESu EZe)) , (x , y) ) =   le x y
              evalOneStep bool ((ESu (ESu (ESu ()))) , _) 


--********************************
-- Open terms
--********************************

Var : EnumU -> Type -> Set
Var dom _ = EnumT dom

openTerm : EnumU -> Type -> IDesc Type
openTerm dom = exprIDesc (\ty -> Val ty + Var dom ty) expr

--********************************
-- Evaluation of open terms
--********************************

discharge : (ty : Type)
          (vars : EnumU)
          (context : spi vars (\_ -> IMu closeTerm ty)) ->
          (Val ty + Var vars ty) -> 
          IMu closeTerm ty
discharge ty vars context (l value) = con ( EZe , value )
discharge ty vars context (r variable) = switch vars (\_ -> IMu closeTerm ty) context variable 


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
        desc (toIDesc I (R ** X) i) (IMu (toIDesc I (R ** Y))) ->
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

exprFreeFixMenu : FixMenu Type
exprFreeFixMenu = ( consE nilE , 
                    \ty -> (prod (var bool) (prod (var ty) (var ty)), 
                           Void))

choiceFreeMenu : Type -> EnumU
choiceFreeMenu nat = consE nilE
choiceFreeMenu bool = consE nilE

choiceFreeDessert : (ty : Type) -> spi (choiceFreeMenu ty) (\ _ -> IDesc Type)
choiceFreeDessert nat = (prod (var nat) (var nat) , Void)
choiceFreeDessert bool = (prod (var nat) (var nat) , Void )

exprFreeSensitiveMenu : SensitiveMenu Type
exprFreeSensitiveMenu = ( choiceFreeMenu ,  choiceFreeDessert )

exprFree : TagIDesc Type
exprFree = exprFreeFixMenu , exprFreeSensitiveMenu

exprFreeC : (Type -> Set) -> TagIDesc Type
exprFreeC X = exprFree ** X

closeTerm' : Type -> IDesc Type
closeTerm' = toIDesc Type (exprFree ** Val)

openTerm' : EnumU -> Type -> IDesc Type
openTerm' dom = toIDesc Type (exprFree ** (\ty -> Val ty + Var dom ty))

--********************************
-- Evaluation of open terms'
--********************************

discharge' : (ty : Type)
            (vars : EnumU)
            (context : spi vars (\_ -> IMu closeTerm' ty)) ->
            (Val ty + Var vars ty) -> 
            IMu closeTerm' ty
discharge' ty vars context (l value) = con (EZe , value) 
discharge' ty vars context (r variable) = switch vars (\_ -> IMu closeTerm' ty) context variable

chooseDom : (ty : Type)(domNat domBool : EnumU) -> EnumU
chooseDom nat domNat _ = domNat
chooseDom bool _ domBool = domBool

chooseGamma : (ty : Type)
              (dom : EnumU)
              (gammaNat : spi dom (\_ -> IMu closeTerm' nat))
              (gammaBool : spi dom (\_ -> IMu closeTerm' bool)) ->
              spi dom (\_ -> IMu closeTerm' ty)
chooseGamma nat dom gammaNat gammaBool = gammaNat
chooseGamma bool dom gammaNat gammaBool = gammaBool

substExpr : (dom : EnumU)
            (gammaNat : spi dom (\_ -> IMu closeTerm' nat))
            (gammaBool : spi dom (\_ -> IMu closeTerm' bool))
            (sigma : (dom : EnumU)
                     (gammaNat : spi dom (\_ -> IMu closeTerm' nat))
                     (gammaBool : spi dom (\_ -> IMu closeTerm' bool))
                     (ty : Type) ->
                     (Val ty + Var dom ty) ->
                     IMu closeTerm' ty)
            (ty : Type) ->
            IMu (openTerm' dom) ty ->
            IMu closeTerm' ty
substExpr dom gammaNat gammaBool sig ty term = 
    substI (\ty -> Val ty + Var dom ty)
           Val
           exprFree
           (sig dom gammaNat gammaBool)
           ty
           term


sigmaExpr : (dom : EnumU)
            (gammaNat : spi dom (\_ -> IMu closeTerm' nat))
            (gammaBool : spi dom (\_ -> IMu closeTerm' bool))
            (ty : Type) ->
            (Val ty + Var dom ty) ->
            IMu closeTerm' ty
sigmaExpr dom gammaNat gammaBool ty v = 
    discharge' ty
               dom
               (chooseGamma ty dom gammaNat gammaBool)
               v

test : IMu (openTerm' (consE (consE nilE))) nat ->
       IMu closeTerm' nat
test term = substExpr (consE (consE nilE)) 
                      ( con ( EZe , ze ) , ( con (EZe , su ze ) , Void )) 
                      ( con ( EZe , true ) , ( con ( EZe , false ) , Void ))
                      sigmaExpr nat term
