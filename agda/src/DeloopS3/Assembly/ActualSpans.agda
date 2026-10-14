{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.ActualSpans where

-- The all-τ₂ cube for the geometric pushout E, with source Bundle.Mₑ.
-- The mixed Bπ₁ cube uses the canonical τ₂ A → τ₁ A equivalence from
-- TruncationLevel; P₂ is distinct from Bπ₁ and E from Local.EO.E_O.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Int using (pos)
open import Cubical.HITs.Pushout.Base using (Pushout; inl)
open import Cubical.HITs.S3 using (S³)
open import DeloopS3.Sphere.TruncationCartesian
import DeloopS3.Sphere.RP2UnitFiber as RP
import DeloopS3.Seifert.TwistedBundle.Cell as Cell
import DeloopS3.Cert.Interpret.Done as Done
import DeloopS3.Assembly.CartesianPushout as Descent

open Done public using (ShortCase; octa; icosa; exponentOf)

R N : Type
R = RP.RP²
N = τ₂ R

r₀ : R
r₀ = RP.rpBase

n₀ : N
n₀ = η₂ r₀

F : Type
F = fiber (η₂ {A = R}) n₀

f₀ : F
f₀ = r₀ , refl

-- Unpointed, in the HITs.S3 model.  Do not silently treat this as a
-- pointed equivalence to (S₊ 3 , north).
F≃S³ : F ≃ S³
F≃S³ = RP.RP²-unit-fiber

A C : ShortCase → Type
A c = Cell.Bundle.Mₑ (pos (exponentOf c))
C = Done.M_G

q : (c : ShortCase) → A c → R
q c = Cell.Bundle.pₑ (pos (exponentOf c))

p : (c : ShortCase) → A c → C c
p = Done.p

E : ShortCase → Type
E c = Pushout (q c) (p c)

iR : (c : ShortCase) → R → E c
iR c = inl

e₀ : (c : ShortCase) → E c
e₀ c = iR c r₀

q-groupoid-fibres : (c : ShortCase) (r : R) → isGroupoid (fiber (q c) r)
q-groupoid-fibres c = Cell.Bundle.fibre-groupoid (pos (exponentOf c))

p-set-fibres : (c : ShortCase) (z : C c) → isSet (fiber (p c) z)
p-set-fibres = Done.p-is-cover

left₂-cartesian : (c : ShortCase)
  → CartSquare (q c) (τ₂-map (q c)) η₂ η₂ (trunc₂-naturality (q c))
left₂-cartesian c = Cell.Bundle.truncation-cartesian (pos (exponentOf c))

right₂-cartesian : (c : ShortCase)
  → CartSquare (p c) (τ₂-map (p c)) η₂ η₂ (trunc₂-naturality (p c))
right₂-cartesian c = trunc₂-cartesian (p c)
  (λ z → isSet→isGroupoid (p-set-fibres c z))

-- The B-cartesian square supplies the mixed cube without a new cover
-- or an unrelated classifying-space model.
right₁-cartesian : (c : ShortCase)
  → CartSquare (p c) (τ₁-map (p c)) η₁ η₁ (trunc₁-naturality (p c))
right₁-cartesian = Done.B-cartesian

module All₂ (c : ShortCase) where
  module Cube = Descent.CartesianPushout
    (q c) (p c) (τ₂-map (q c)) (τ₂-map (p c))
    η₂ η₂ η₂ (trunc₂-naturality (q c)) (trunc₂-naturality (p c))
    (left₂-cartesian c) (right₂-cartesian c)

  open Cube public using
    (P; t; J; J-isEquiv; λB; λB-isEquiv; λC; λC-isEquiv;
     descend-left; descend-right)

  local-fibre : F ≃ fiber t (inl n₀)
  local-fibre = λB n₀ , λB-isEquiv n₀

  sphere-fibre : fiber t (inl n₀) ≃ S³
  sphere-fibre = compEquiv (invEquiv local-fibre) F≃S³
