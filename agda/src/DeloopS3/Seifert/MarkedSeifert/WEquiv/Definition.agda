{-# OPTIONS --safe --cubical #-}

-- The literal three-torus / three-circle Seifert pushout.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.Data.Int using (ℤ; pos; _-_)
open import Cubical.HITs.Pushout.Base
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Cover.Orientation.CircleModel using (hC; CToCircle)
open import DeloopS3.Seifert.MarkedSeifert.WInterface public using (row; W)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Shapes using (module Stage)

wedgeLeg : Unit → C
wedgeLeg _ = 0C

P : Type₀
P = Pushout wedgeLeg wedgeLeg

p₀ : P
p₀ = inl 0C

edge : Path P (inl 0C) (inr 0C)
edge = push tt

d₁ d₂ : C → P
d₁ = inl
d₂ = inr

a b : p₀ ≡ p₀
a = cong d₁ hC
b = (edge ∙ cong d₂ hC) ∙ sym edge

d₃ : C → P
d₃ = circleMap (sym (a ∙ b)) ∘ CToCircle

Core : Type₀
Core = P × C

boundary₁ boundary₂ boundary₃ : T² → Core
boundary₁ (u , t) = d₁ u , t
boundary₂ (u , t) = d₂ u , t
boundary₃ (u , t) = d₃ u , t

left12 : T² ⊎ T² → Core
left12 (left z) = boundary₁ z
left12 (right z) = boundary₂ z

right12 : ℤ → ℤ → T² ⊎ T² → C ⊎ C
right12 p q (left z) = left (row (pos 1) p z)
right12 p q (right z) = right (row (pos 1) q z)

FirstTwoFillings : Type₀
FirstTwoFillings = Pushout left12 (right12 (pos 2) (pos 2))

-- Three disjoint tori and three disjoint core circles, grouped ((1,2),3).
module Seifert (p q r : ℤ) where
  module S = Stage {ℓ = ℓ-zero} {L = Core}
    {A = T² ⊎ T²} {B = T²} {R = C ⊎ C} {S = C}
    left12 boundary₃ (right12 p q) (row (pos 1 - r) r)
  open S public using (allLeft; allRight)
  Total : Type₀
  Total = Pushout allLeft allRight

M : ℤ → ℤ → ℤ → Type₀
M p q r = Seifert.Total p q r

M22e : ℤ → Type₀
M22e e = M (pos 2) (pos 2) e

thirdOriginal : T² → FirstTwoFillings
thirdOriginal = inl ∘ boundary₃
