{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The RP¹ cover, its circle chart, and the sign-circle boundary total.
module DeloopS3.Seifert.TwistedBundle.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.RPn.Base using (RP; cov⁻¹; TotalCov≃Sn)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.Susp.Base using (BoolIsoSusp⊥; S¹IsoSuspBool)
open import Cubical.HITs.Susp.Properties using (congSuspIso)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Fibration using (fiberEquiv)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (addIso)
open import DeloopS3.Move.CancelMinimal using (C; 0C; mulC; _+C_)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Sphere.RP2UnitFiber using (RP²; rpBase; RP²-unit-fiber)
open import DeloopS3.Sphere.TruncationCartesian
open import Cubical.HITs.S3 using (S³)

R : Type
R = RP 1

w₁ : R → B
w₁ = cov⁻¹ 1

A : Type
A = Σ R (λ x → fst (w₁ x))

pr₁ : A → R
pr₁ = fst

cap : A → Unit
cap _ = tt

δ : A → A
δ (x , y) = x , op (w₁ x) y

δ-invol : (a : A) → δ (δ a) ≡ a
δ-invol (x , y) = ΣPathP (refl , op-invol (w₁ x) y)

-- This circle equivalence does not fix the sign relative to the four-edge
-- tree chart. Chart.H retains its actual vertex paths in the deck homotopy.
abstract
  fA : A ≃ C
  fA = compEquiv (TotalCov≃Sn 1)
    (compEquiv (invEquiv (isoToEquiv
      (compIso S¹IsoSuspBool (congSuspIso BoolIsoSusp⊥)))) S¹≃C)

  -- Export the defining comparison without changing the existing chart.
  -- Its vertex paths must be transported, not replaced by tree-chart refls.
  fA-unfold : fA ≡ compEquiv (TotalCov≃Sn 1)
    (compEquiv (invEquiv (isoToEquiv
      (compIso S¹IsoSuspBool (congSuspIso BoolIsoSusp⊥)))) S¹≃C)
  fA-unfold = refl

Ksign : Type
Ksign = Σ R (SignC ∘ w₁)

λA : A × C → Ksign
λA ((x , z) , t) = x , invEq (ε (w₁ x) z) t

