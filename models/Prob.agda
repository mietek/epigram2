 {-# OPTIONS --type-in-type #-}

module Prob where

open import DescTT

mutual
  data Sch : Set where
    ty   : (S : Set) -> Sch
    exPi : (s : Sch)(T : toType s -> Sch) -> Sch
    imPi : (S : Set)(T : S -> Sch) -> Sch

  toType : Sch -> Set
  toType (ty S)     = S
  toType (exPi s T) = (x : toType s) -> toType (T x)
  toType (imPi S T) = (x : S) -> toType (T x)


Args : Sch -> Set
Args (ty _)     = Unit
Args (exPi s T) = Sigma (toType s) \ x -> Args (T x)
Args (imPi S T) = Sigma S \ x -> Args (T x)


postulate
  UId : Set
  Prp : Set
  Prf : Prp -> Set

data Prob : Set where
  label : (u : UId)(s : Sch)(a : Args s) -> Prob
  patPi : (u : UId)(S : Set)(p : Prob) -> Prob
  hypPi : (p : Prp)(T : Prf p -> Prob) -> Prob
  recPi : (rec : Prob)(p : Prob) -> Prob