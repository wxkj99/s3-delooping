{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.RP2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Nat using (ℕ ; _+_ ; +-comm)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Int using (pos)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; pushoutEquiv ; symPushout)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.Recognition.Degree using (degree-deg₁)
open import DeloopS3.Bridge.ComponentHomology.Finite using (RP²CW ; RP²-finite)
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre
open import DeloopS3.Local.Base using (deg₁)
open import DeloopS3.Local.Powers using (cong-powLoop)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
import DeloopS3.Seifert.TwistedBundle.Base as RP
import DeloopS3.Seifert.TwistedBundle.Chart as Ch
open import DeloopS3.Seifert.MarkedSeifert.DescentChart using
  (rCircle ; rCircle-isEquiv ; aCircle₀ ; aCircle₀-isEquiv)

cofibre-circle : S¹ → cofib (deg₁ 2)
cofibre-circle = inr

RP¹-inclusion : RP.R → RP²
RP¹-inclusion = inl

-- The existing four-edge chart is a proved equivalence of the ACTUAL
-- Total(cov⁻¹ 1).  Its projection traverses the marked two-edge loop twice.
abstract
  projection-degree-two : RP.pr₁ ∘ aCircle₀ ≡ rCircle ∘ deg₁ 2
  projection-degree-two = funExt λ
    { base → refl
    ; (loop i) → λ j →
      (Ch.w-projects ∙ cong (Ch.t ∙_) (rUnit Ch.t)
        ∙ sym (cong-powLoop rCircle 2 loop)) j i }

  circle-cofibre≃RP² : cofib (deg₁ 2) ≃ RP²
  circle-cofibre≃RP² = compEquiv (symPushout (λ _ → tt) (deg₁ 2))
    (pushoutEquiv (deg₁ 2) (λ _ → tt) RP.pr₁ RP.cap
      (aCircle₀ , aCircle₀-isEquiv) (rCircle , rCircle-isEquiv)
      (idEquiv Unit) (sym projection-degree-two) refl)

  -- The adapter retains t, rather than only an unpointed homotopy type.
  circle-cofibre-base : fst circle-cofibre≃RP² (inr base) ≡ inl (RP.pr₁ Ch.L₀)
  circle-cofibre-base = refl

  circle-cofibre-loop : PathP
    (λ i → circle-cofibre-base i ≡ circle-cofibre-base i)
    (cong (fst circle-cofibre≃RP²) (cong cofibre-circle loop))
    (cong RP¹-inclusion Ch.t)
  circle-cofibre-loop = refl

  RP²-H₀ : Hzero RP²CW 0
  RP²-H₀ = circle-cofibre-H₀ (deg₁ 2) RP²CW (invEquiv circle-cofibre≃RP²)

  RP²-H₁ : GroupEquiv (H̃ᶜʷ RP²CW 1) (ℤGroup/ 2)
  RP²-H₁ = circle-cofibre-H₁ (deg₁ 2) RP²CW
    (invEquiv circle-cofibre≃RP²) 2 (degree-deg₁ 2)

  RP²-H₂ : Hzero RP²CW 2
  RP²-H₂ = circle-cofibre-H₂ (deg₁ 2) RP²CW
    (invEquiv circle-cofibre≃RP²) 1 (degree-deg₁ 2) refl

  RP²-H≥3 : (n : ℕ) → Hzero RP²CW (3 + n)
  RP²-H≥3 n = finite≤-homology-above RP²CW 2 (3 + n)
    RP²-finite (n , +-comm n 3)
