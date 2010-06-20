module Records where

data Sigma (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) (y : B x) -> Sigma A B

fst : {A : Set}{B : A -> Set} -> Sigma A B -> A
fst (x , y) = x

snd : {A : Set}{B : A -> Set} -> (p : Sigma A B) -> B (fst p)
snd (x , y) = y

data Sigma1 (A : Set1) (B : A -> Set1) : Set1 where
  _,_ : (x : A) (y : B x) -> Sigma1 A B

fst1 : {A : Set1}{B : A -> Set1} -> Sigma1 A B -> A
fst1 (x , y) = x

snd1 : {A : Set1}{B : A -> Set1} -> (p : Sigma1 A B) -> B (fst1 p)
snd1 (x , y) = y

data Zero : Set where
data Unit  : Set where
  Void : Unit

data Test1 : Set where
data Test2 : Set where
data Test3 : Set where


data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Fin : Nat -> Set where
  fze : {n : Nat} -> Fin (su n) 
  fsu : {n : Nat} -> Fin n -> Fin (su n)

mutual 
  data Sig : Set1 where
    Epsilon : Sig 
    _<_ : (S : Sig)(A : [| S |] -> Set) -> Sig 


  [|_|] : Sig -> Set
  [| Epsilon |] = Unit
  [| S < A |] = Sigma [| S |] A

size : Sig -> Nat
size Epsilon = ze
size (S < A) = su (size S)

typeAt : (S : Sig) -> Fin (size S) -> Sigma1 Sig (\ S -> [| S |] -> Set)
typeAt Epsilon ()
typeAt (S < A) fze = ( S , A )
typeAt (S < A) (fsu y) = typeAt S y

fsts : (S : Sig)(i : Fin (size S)) -> [| S |] -> [| fst1 (typeAt S i) |]
fsts Epsilon () rec
fsts (S < A) fze rec = fst rec
fsts (S < A) (fsu y) rec = fsts S y (fst rec)

at : (S : Sig)(i : Fin (size S))(rec : [| S |]) -> snd1 (typeAt S i) (fsts S i rec)
at Epsilon () rec
at (S < A) fze rec = snd rec
at (S < A) (fsu y) rec = at S y (fst rec) 


-- * Record definition combinators:

-- ** Non dependant case works:

fi : {a : Set1} -> (S : Sig) -> Set -> (Sig -> a) -> a
fi S A k = k (S < (\_ -> A))

begin : {a : Set1} -> (Sig -> a) -> a
begin k = k Epsilon

end : (Sig -> Sig)
end x = x

test : Sig
test = begin fi Test1 fi Test2 fi Test3 end

-- ** Dependant case doesn't:

fiD : {a : Sig -> Set1} -> (S : Sig) -> (A : ([| S |] -> Set)) -> ((S : Sig) -> a S) -> a (S < A)
fiD S A k = k (S < A)

beginD : {a : Sig -> Set1} -> ((S : Sig) -> a S) -> a Epsilon
beginD k = k Epsilon

endD : (Sig -> Sig)
endD x = x


test2 : Sig
test2 = beginD fiD ((\ _ -> Test1)) fiD {!!} fiD {!!} endD