{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Sphere.RP2UnitFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (isSetBool)
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.Susp.Base
  using (north; BoolIsoSusp⊥; S¹IsoSuspBool)
open import Cubical.HITs.Susp.Properties using (congSuspIso)
open import Cubical.HITs.Sn.Base using (S; S₊)
open import Cubical.HITs.S3 using (S³)
open import Cubical.HITs.RPn.Base using (RP; cov; cov⁻¹; fibcov≡cov⁻¹)

open import DeloopS3.Sphere.HopfUnit using (sphereUnitFiber)
open import DeloopS3.Sphere.TruncationCartesian

-- Use the inductive model RP 2, not the separate small RP² HIT.
-- The stock cov is obtained from TotalCov≃Sn.
RP² : Type
RP² = RP 2

-- RP's sphere is the iterated suspension of the empty type; the Hopf
-- calculation uses Susp S¹. This equivalence supplies the model adapter.
S²≃S2 : S₊ 2 ≃ S 2
S²≃S2 = isoToEquiv
  (congSuspIso (compIso S¹IsoSuspBool (congSuspIso BoolIsoSusp⊥)))

q : S₊ 2 → RP²
q = cov 2 ∘ equivFun S²≃S2

q-fiber : (y : RP²) → fiber q y ≃ fst (cov⁻¹ 2 y)
q-fiber y = compEquiv
  (Σ-cong-equiv-fst {B = λ x → cov 2 x ≡ y} S²≃S2)
  (pathToEquiv (fibcov≡cov⁻¹ 2 y))

q-fibers-are-sets : (y : RP²) → isSet (fiber q y)
q-fibers-are-sets y = isOfHLevelRetractFromIso 2 (equivToIso (q-fiber y))
  (PT.rec isPropIsSet
    (λ e → isOfHLevelRetractFromIso 2 (equivToIso e) isSetBool)
    (snd (cov⁻¹ 2 y)))

-- A specified base point together with its specified lift, with no choice.
rpBase : RP²
rpBase = q north

RP²-cover-unit-fibers : (z : τ₂ (S₊ 2))
  → fiber η₂ z ≃ fiber η₂ (τ₂-map q z)
RP²-cover-unit-fibers = trunc₂-unit-fibers q
  (λ y → isSet→isGroupoid (q-fibers-are-sets y))

-- Equation (10.3). No assertion that τ₂ RP² is K(Z,2) is used or made.
RP²-unit-fiber : fiber (η₂ {A = RP²}) (η₂ rpBase) ≃ S³
RP²-unit-fiber = compEquiv
  (invEquiv (RP²-cover-unit-fibers (η₂ north)))
  sphereUnitFiber
