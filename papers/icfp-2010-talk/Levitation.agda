module Levitation where

open import Data.Product

record ⊤ : Set1 where
  constructor tt


data Desc : Set2 where
  `1 : Desc
  `Σ : (S : Set1)(D : S → Desc) → Desc
  `ind× : (D : Desc) → Desc
  `hind× : (H : Set)(D : Desc) → Desc

⟦_⟧ : Desc → Set1 → Set1
⟦ `1 ⟧ X          = ⊤
⟦ `Σ S D ⟧ X      = Σ S (\s → ⟦ D s ⟧ X)
⟦ `ind× D ⟧ X     =  X × ⟦ D ⟧ X
⟦ `hind× H D ⟧ X  = (H → X) × ⟦ D ⟧ X

data Mu (D : Desc) : Set1 where
  con : ⟦ D ⟧ (Mu D) → Mu D

data DescDConst : Set1 where
  ``1 : DescDConst
  ``Σ : DescDConst
  ``ind× : DescDConst
  ``hind× : DescDConst

DescDChoice : DescDConst → Desc
DescDChoice ``1 = `1
DescDChoice ``Σ = `Σ Set (\S → `hind× S `1)
DescDChoice ``ind× = `ind× `1
DescDChoice ``hind× = `Σ Set (\_ → `ind× `1)

DescD : Desc
DescD = `Σ DescDConst DescDChoice

Desc' : Set1
Desc' = Mu DescD

`1' : Desc'
`1' = con (``1 , tt)

`Σ' : (S : Set)(D : S → Desc') → Desc'
`Σ' S D = con (``Σ , (S , (D , tt)))

`ind×' : (D : Desc') → Desc'
`ind×' D = con (``ind× , (D , tt))

`hind×' : (H : Set)(D : Desc') → Desc'
`hind×' H D = con (``hind× , (H , (D , tt)))