{-# OPTIONS --type-in-type --no-termination-check
  #-}

module Containers where

  record Sigma (A : Set) (B : A -> Set) : Set where
    field fst : A
          snd : B fst 

  open Sigma

  _*_ : (A B : Set) -> Set
  A * B = Sigma A \_ -> B

  data Zero : Set where
 
  record One : Set where

  data PROP : Set where
    Absu : PROP
    Triv : PROP
    _/\_ : PROP -> PROP -> PROP
    All : (S : Set) -> (S -> PROP) -> PROP

  Prf : PROP -> Set
  Prf Absu = Zero
  Prf Triv = One
  Prf (P /\ Q) = Prf P * Prf Q
  Prf (All S P) = (x : S) -> Prf (P x)

  _,_ : forall {A B} -> (a : A) -> B a -> Sigma A B
  a , b = record { fst = a ; snd = b }

  split : ∀ {A B} {C : Sigma A B -> Set} -> 
    (f : (a : A) -> (b : B a) -> C (a , b)) -> (ab : Sigma A B) -> C ab 
  split f ab = f (fst ab) (snd ab)

  data _+_ (A B : Set) : Set where
    l : A -> A + B
    r : B -> A + B

  cases : ∀ {A B} {C : A + B -> Set} -> 
            ((a : A) -> C (l a)) -> ((b : B) -> C (r b)) -> 
            (ab : A + B) -> C ab
  cases f g (l a) = f a
  cases f g (r b) = g b 

  rearrange : ∀ {A B X} (C : A → Set) (D : B → Set) (f : Sigma A C → X) → 
              Sigma (A + B) (cases C D) → X + Sigma B D
  rearrange {A} {B} {X} C D f = split {A + B} (cases (\a c → l (f (a , c))) (\b d → r (b , d)))

  data CON (I : Set) : Set where
    ?? : I -> CON I
    PrfC : PROP -> CON I
    _*C_ : CON I -> CON I -> CON I
    PiC : (S : Set) -> (S -> CON I) -> CON I
    SiC : (S : Set) -> (S -> CON I) -> CON I
    MuC : (O : Set) -> (O -> CON (I + O)) -> O -> CON I

  mutual
 
    data Mu {I : Set} (O : Set) (D : O -> CON (I + O)) 
            (X : I -> Set) : O -> Set where
      inm : {o : O} -> [| D o |] (cases X (Mu O D X)) ->  Mu O D X o

    [|_|]_ : {I : Set} -> (CON I) -> (I -> Set) -> Set
    [| ?? i |] X = X i
    [| PrfC p |] X = Prf p
    [| C *C D |] X = [| C |] X * [| D |] X
    [| PiC S C |] X = (s : S) -> [| C s |] X
    [| SiC S C |] X = Sigma S \s -> [| C s |] X
    [| MuC O C o |] X = Mu O C X o


  outm : {I O : Set} {D : O -> CON (I + O)} {X : I -> Set} {o : O} ->
    Mu O D X o -> [| D o |]  (cases X (Mu O D X))
  outm (inm x) = x 


  Everywhere : {I : Set} -> (D : CON I) -> (J : I -> Set) -> (X : Set) ->  
               (Sigma I J -> X) ->  [| D |] J -> CON X
  Everywhere (?? i) J X c t = ?? (c (i , t))
  Everywhere (PrfC p) J X c t = PrfC Triv
  Everywhere (C *C D) J X c t = 
    Everywhere C J X c (fst t) *C Everywhere D J X c (snd t)
  Everywhere (PiC S C) J X c t = PiC S (\s -> Everywhere (C s) J X c (t s))
  Everywhere (SiC S C) J X c t = Everywhere (C (fst t)) J X c (snd t)
  Everywhere (MuC O C o) J X c t = MuC (Sigma O (Mu O C J)) (\ot' -> 
        Everywhere (C (fst ot')) 
                   (cases J (Mu O C J)) 
                   (X + (Sigma O (Mu O C J)))
                   (split (cases(\i j -> l (c (i , j))) 
                                (\o'' t'' -> r (o'' , t'')))) 
                   (outm (snd ot'))) 
     (o , t)

  everywhere : {I : Set} -> (D : CON I) -> (J : I -> Set) -> (X : Set) ->
               (c : Sigma I J -> X) -> (Y : X -> Set) -> 
               (f : (ij : Sigma I J) -> Y (c ij)) -> (t : [| D |] J) -> 
               [| Everywhere D J X c t |] Y
  everywhere (?? i) J X c Y f t = f (i , t)
  everywhere (PrfC p) J X c Y f t = _
  everywhere (C *C D) J X c Y f t = 
    everywhere C J X c Y f (fst t) , everywhere D J X c Y f (snd t)
  everywhere (PiC S C) J X c Y f t = \s -> everywhere (C s) J X c Y f (t s)
  everywhere (SiC S C) J X c Y f t = everywhere (C (fst t)) J X c Y f (snd t)
  everywhere (MuC O C o) J X c Y f (inm t) = 
    inm (everywhere (C o) (cases J (Mu O C J)) (X + Sigma O (Mu O C J)) (
        (split (cases (\i j -> l (c (i , j))) (\o t -> r (o , t))))) 
        (cases Y (split \o'' t'' -> [| Everywhere (MuC O C o'') J X c t'' |] Y))
        (split (cases (\i j -> f (i , j)) 
                      (\o'' t'' -> everywhere (MuC O C o'') J X c Y f t''))) 
        t)
 
  induction : {I O : Set} (D : O -> CON (I + O)) (J : I -> Set) (X : Set) 
              (c : Sigma I J -> X) (Y : X -> Set) (f : (ij : Sigma I J) -> Y (c ij)) 
              (P : Sigma O (Mu O D J) -> Set) ->
              ({o : O} (v : [| D o |] cases J (Mu O D J)) -> 
               [| Everywhere (D o) _ (X + Sigma O (Mu O D J)) 
                             (split (cases (\i j -> l (c (i , j))) 
                             (\o v -> r (o , v)))) v |] cases Y P -> 
               P (o , inm v)) ->
              (o : O) (v : Mu O D J o) -> P (o , v)
  induction {I} {O} D J X c Y f P p o (inm v) = 
    p v (everywhere {I + O} (D o) 
                    (λ x -> cases {I} {O} {\_ -> Set} J 
                    (Mu O D J) x) ((X + Sigma O (Mu O D J))) 
                    (rearrange J (Mu O D J) c) (cases Y P) 
                    (split {I + O} (cases (\i j -> f (i , j)) 
                    (\o v -> induction D J X c Y f P p o v))) v) 