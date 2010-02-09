{-# OPTIONS --type-in-type
            --no-termination-check
            --no-positivity-check #-}

module IMDesc where

--********************************************
-- Prelude
--********************************************

-- Some preliminary stuffs, to avoid relying on the stdlib

--****************
-- Sigma and friends
--****************

data Sigma (A : Set)(B : A -> Set) : Set where
  _,_ : (x : A)(y : B x) -> Sigma A B

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

--****************
-- Prop
--****************

data EProp : Set where
  Trivial : EProp
  
Prf : EProp -> Set
Prf _ = {! !}

--****************
-- Enum
--****************

data EnumU : Set where
  
data EnumT (E : EnumU) : Set where

Branches : (E : EnumU) -> (P : EnumT E -> Set) -> Set
Branches  _ _ = {! !}

switch : (E : EnumU) -> (e : EnumT E) -> (P : EnumT E -> Set) -> Branches E P -> P e
switch = {! !}




--********************************************
-- IMDesc
--********************************************


--****************
-- Code
--****************

data IDesc (I : Set) : Set where
  iat      : (i : I) -> IDesc I
  ipi      : (S : Set)(T : S -> IDesc I) -> IDesc I
  isigma   : (S : Set)(T : S -> IDesc I) -> IDesc I
  iprf     : (Q : EProp) -> IDesc I
  iprod    : (D : IDesc I)(D : IDesc I) -> IDesc I
  ifsigma  : (E : EnumU)(f : Branches E (\ _ -> IDesc I)) -> IDesc I

--****************
-- Interpretation
--****************

desc : (I : Set)(D : IDesc I)(P : I -> Set) -> Set
desc I (iat i)        P = P i
desc I (ipi S T)      P = (s : S) -> desc I (T s) P
desc I (isigma S T)   P = Sigma S (\ s -> desc I (T s) P)
desc I (iprf q)       P = Prf q
desc I (iprod D D')   P = Sigma (desc I D P) (\ _ -> desc I D' P)
desc I (ifsigma E B)  P = Sigma (EnumT E) (\ e -> desc I (switch E e (\ _ -> IDesc I) B) P)

--****************
-- Curried and uncurried interpretations
--****************

curryD : (I : Set)(D : IDesc I)(P : I -> Set)(R : desc I D P -> Set) -> Set
curryD I (iat i) P R = (x : P i) -> R x
curryD I (ipi S T) P R = (f : (s : S) -> desc I (T s) P) -> R f
curryD I (isigma S T) P R = (s : S) -> curryD I (T s) P (\ d -> R (s , d))
curryD I (iprf Q) P R = (x : Prf Q) -> R x
curryD I (iprod D D') P R = curryD I D P (\ d ->
                             curryD I D' P (\ d' -> R (d , d')))
curryD I (ifsigma E B) P R = Branches E (\e -> curryD I (switch E e (\_ -> IDesc I) B) P (\d -> R (e , d)))



uncurryD : (I : Set)(D : IDesc I)(P : I -> Set)(R : desc I D P -> Set) ->
           curryD I D P R -> (xs : desc I D P) -> R xs
uncurryD I (iat i) P R f xs = f xs
uncurryD I (ipi S T) P R F f = F f
uncurryD I (isigma S T) P R f (s , d) =  uncurryD I (T s) P (\d -> R (s , d)) (f s) d
uncurryD I (iprf Q) P R f q = f q 
uncurryD I (iprod D D') P R f (d , d') =  uncurryD I D' P ((\ d' → R (d , d'))) 
                                           (uncurryD I D P ((\ x → curryD I D' P (\ d0 → R (x , d0)))) f d) d'
uncurryD I (ifsigma E B) P R br (e , d) =  uncurryD I (switch E e (\ _ -> IDesc I) B) P 
                                                      (\ d -> R ( e , d )) 
                                                      (switch E e ( \ e -> R ( e , d)) br) d


--****************
-- Everywhere
--****************

box : (I : Set)(D : IDesc I)(P : I -> Set) -> desc I D P -> IDesc (Sigma I P)
box I (iat i)        P x         = iat (i , x)
box I (ipi S T)      P f         = ipi S (\ s -> box I (T s) P (f s))
box I (isigma S T)   P (s , d)   = box I (T s) P d
box I (iprf Q)       P q         = iprf Trivial
box I (iprod D D')   P (d , d')  = iprod (box I D P d) (box I D' P d')
box I (ifsigma E B)  P (e , d)   = box I (switch E e (\ _ -> IDesc I) B) P d

mapbox : (I : Set)(D : IDesc I)(Z : I -> Set)(P : Sigma I Z -> Set) ->
         ((x : Sigma I Z) -> P x) ->
         ( d : desc I D Z) -> desc (Sigma I Z) (box I D Z d) P
mapbox = {!!}


--****************
-- Fix-point
--****************


data IMu (I : Set)(D : I -> IDesc I)(i : I) : Set where
  Con : desc I (D i) (\ j -> IMu I D j) -> IMu I D i


--****************
-- Induction, curried
--****************


inductionC : (I : Set)(D : I -> IDesc I)(i : I)(v : IMu I D i)
             (P : Sigma I (IMu I D) -> Set)
             (m : (i : I) -> 
                  curryD I (D i) (IMu I D) (\xs ->
                    curryD (Sigma I (IMu I D))
                           (box I (D i) (IMu I D) xs) 
                           P 
                           (\ _ -> P (i , Con xs)))) ->
             P ( i , v )
inductionC I D i (Con x) P m = 
  let t = uncurryD  I
                    (D i)
                    (IMu I D) 
                    (\xs ->
                    curryD (Sigma I (IMu I D))
                           (box I (D i) (IMu I D) xs) 
                           P 
                           (\ _ -> P (i , Con xs)))
                    (m i)
                    x 
  in
  uncurryD (Sigma I (IMu I D))
           ( box I (D i) (IMu I D) x)
           P
           (\ _ -> P ( i , Con x))
           t
           (mapbox I ( D i) ( IMu I D) P ind x)
           where ind : (x' : Sigma I (IMu I D)) -> P x'
                 ind ( i , x) = inductionC I D i x P m
