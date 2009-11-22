{-# OPTIONS --type-in-type
            --no-termination-check
            --no-positivity-check #-}

module Desc where

--********************************************
-- Prelude
--********************************************

-- Some preliminary stuffs, to avoid relying on the stdlib

--****************
-- Sigma and friends
--****************

data Sigma (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) -> Sigma A B

_*_ : (A B : Set) -> Set
A * B = Sigma A \_ -> B

fst : {A : Set}{B : A -> Set} -> Sigma A B -> A
fst (a , _) = a

snd : {A : Set}{B : A -> Set} (p : Sigma A B) -> B (fst p)
snd (a , b) = b

data Zero : Set where
record One : Set where

--****************
-- Sum and friends
--****************

data _+_ (A B : Set) : Set where
  l : A -> A + B
  r : B -> A + B



--********************************************
-- Desc code
--********************************************

-- Inductive types are implemented as a Universe. Hence, in this
-- section, we implement their code.

-- We can read this code as follow (see Conor's "Ornamental
-- algebras"): a description in |Desc| is a program to read one node
-- of the described tree.

data Desc : Set where
  Arg : (X : Set) -> (X -> Desc) -> Desc
  -- Read a field in |X|; continue, given its value

  -- Often, |X| is an |EnumT|, hence allowing to choose a constructor
  -- among a finite set of constructors

  Ind : (H : Set) -> Desc -> Desc
  -- Read a field in H; read a recursive subnode given the field,
  -- continue regarless of the subnode

  -- Often, |H| is |1|, hence |Ind| simplifies to |Inf : Desc -> Desc|,
  -- meaning: read a recursive subnode and continue regardless

  Done : Desc
  -- Stop reading


--********************************************
-- Desc decoder
--********************************************

-- Provided the type of the recursive subnodes |R|, we decode a
-- description as a record describing the node.

[|_|]_ : Desc -> Set -> Set
[| Arg A D |] R = Sigma A (\ a -> [| D a |] R)
[| Ind H D |] R = (H -> R) * [| D |] R
[| Done |] R = One


--********************************************
-- Functions on codes
--********************************************

-- Saying that a "predicate" |p| holds everywhere in |v| amounts to
-- write something of the following type:

Everywhere : (d : Desc) (D : Set) (bp : D -> Set) (V : [| d |] D) -> Set
Everywhere (Arg A f) d p v =  Everywhere (f (fst v)) d p (snd v)
-- It must hold for this constructor

Everywhere (Ind H x) d p v =  ((y : H) -> p (fst v y)) * Everywhere x d p (snd v)
-- It must hold for the subtrees 

Everywhere Done _ _ _ =  _
-- It trivially holds at endpoints

-- Then, we can build terms that inhabits this type. That is, a
-- function that takes a "predicate" |bp| and makes it hold everywhere
-- in the data-structure. It is the equivalent of a "map", but in a
-- dependently-typed setting.

everywhere : (d : Desc) (D : Set) (bp : D -> Set) ->
           ((y : D) -> bp y) -> (v : [| d |] D) ->
           Everywhere d D bp v
everywhere (Arg a f) d bp p v =  everywhere (f (fst v)) d bp p (snd v)
-- It holds everywhere on this constructor

everywhere (Ind H x) d bp p v = (\y -> p (fst v y)) ,  everywhere x d bp p (snd v)
-- It holds here, and down in the recursive subtrees

everywhere Done _ _ _ _ =  One
-- Nothing needs to be done on endpoints


-- Looking at the decoder, a natural thing to do is to define its
-- fixpoint |Mu D|, hence instantiating |R| with |Mu D| itself.

data Mu (D : Desc) : Set where
  Con : [| D |] (Mu D) -> Mu D

-- Using the "map" defined by |everywhere|, we can implement a "fold"
-- over the |Mu| fixpoint:

foldDesc : (D : Desc) (bp : Mu D -> Set) ->
         ((x : [| D |] (Mu D)) -> Everywhere D (Mu D) bp x -> bp (Con x)) ->
         (v : Mu D) ->
         bp v
foldDesc D bp p (Con v) =  p v (everywhere D (Mu D) bp (\x -> foldDesc D bp p x) v) 


--********************************************
-- Nat
--********************************************

data NatConst : Set where
  ZE : NatConst
  SU : NatConst

natc : NatConst -> Desc
natc ZE = Done
natc SU = Ind One Done

natd : Desc
natd = Arg NatConst natc

nat : Set
nat = Mu natd

zero : nat
zero = Con ( ZE ,  _ )

suc : nat -> nat
suc n = Con ( SU , ( (\_ -> n) ,  _ ) )

two : nat
two = suc (suc zero)

four : nat
four = suc (suc (suc (suc zero)))

sum : nat -> 
      ((x : Sigma NatConst (\ a -> [| natc a |] Mu (Arg NatConst natc))) ->
      Everywhere (natc (fst x)) (Mu (Arg NatConst natc)) (\ _ -> Mu (Arg NatConst natc)) (snd x) ->
      Mu (Arg NatConst natc))
sum n2 (ZE , _) p =  n2
sum n2 (SU , f) p =  suc ( fst p _) 


plus : nat -> nat -> nat
plus n1 n2 = foldDesc natd (\_ -> nat) (sum n2) n1 

x : nat
x = plus two two



