{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.TruncationLevel where

-- The comparison is the canonical truncation recursor;
-- its equivalence proof does not choose a different map or a π₁ model.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (lCancel)
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Int using (pos; abs)
open import Cubical.Data.Nat using (snotz)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Homotopy.Group.Base using (π; πTruncIso)
open import Cubical.HITs.SetTruncation using (setTruncIdempotentIso)
import Cubical.HITs.Truncation as Tr
open import DeloopS3.Sphere.TruncationCartesian using (τ₁; τ₂; η₁; η₂)
import DeloopS3.Assembly.ActualSpans as Actual
import DeloopS3.Seifert.MarkedSeifert.Final as Final

κ : ∀ {ℓ} {X : Type ℓ} → τ₂ X → τ₁ X
κ = Tr.rec (isOfHLevelSuc 3 (Tr.isOfHLevelTrunc 3)) η₁

κ-η : ∀ {ℓ} {X : Type ℓ} (x : X) → κ (η₂ x) ≡ η₁ x
κ-η x = refl

private
  -- Translate a loop p to refl by left multiplication with p⁻¹.
  -- Keep this argument generic, outside all geometric specializations.
  abstract
    loop-self-contr : ∀ {ℓ} {Y : Type ℓ} (y : Y)
      → isContr (refl {x = y} ≡ refl)
      → (p : y ≡ y) → isContr (p ≡ p)
    loop-self-contr y h p = isOfHLevelRespectEquiv 0
      (invEquiv (congEquiv {x = p} {y = p} (compPathlEquiv (sym p))))
      (subst (λ (z : y ≡ y) → isContr (z ≡ z)) (sym (lCancel p)) h)

    double-loops-contr→groupoid : ∀ {ℓ} (Y : Type ℓ)
      → ((y : Y) → isContr (refl {x = y} ≡ refl)) → isGroupoid Y
    double-loops-contr→groupoid Y h = isOfHLevelΩ→isOfHLevel 1
      (λ y → isOfHLevelΩ→isOfHLevel 0
        (λ p → isContr→isProp (loop-self-contr y (h y) p)))

    trunc₂-double-loops-at-unit : ∀ {ℓ} (X : Type ℓ) (x : X)
      → isContr (π 2 (X , x))
      → isContr (refl {x = η₂ x} ≡ refl)
    trunc₂-double-loops-at-unit X x h = isOfHLevelRespectEquiv 0
      (compEquiv
        (isoToEquiv (πTruncIso {A = X , x} 2))
        (isoToEquiv (setTruncIdempotentIso
          (Tr.isOfHLevelTrunc 4 (η₂ x) (η₂ x) refl refl)))) h

abstract
  trunc₂-groupoid-from-π₂ : ∀ {ℓ} (X : Type ℓ)
    → ((x : X) → isContr (π 2 (X , x))) → isGroupoid (τ₂ X)
  trunc₂-groupoid-from-π₂ X h = double-loops-contr→groupoid (τ₂ X)
    (Tr.elim {B = λ y → isContr (refl {x = y} ≡ refl)}
      (λ y → isProp→isOfHLevelSuc 3 isPropIsContr)
      (λ x → trunc₂-double-loops-at-unit X x (h x)))

  κ-isEquiv-from-groupoid : ∀ {ℓ} (X : Type ℓ)
    → isGroupoid (τ₂ X) → isEquiv (κ {X = X})
  κ-isEquiv-from-groupoid X h = isoToIsEquiv (iso κ j κ-j j-κ)
    where
    j : τ₁ X → τ₂ X
    j = Tr.rec h η₂

    κ-j : (z : τ₁ X) → κ (j z) ≡ z
    κ-j = Tr.elim
      (λ z → isOfHLevelPath 3 (Tr.isOfHLevelTrunc 3) (κ (j z)) z)
      (λ x → refl)

    j-κ : (z : τ₂ X) → j (κ z) ≡ z
    j-κ = Tr.elim
      (λ z → isOfHLevelPath 4 (Tr.isOfHLevelTrunc 4) (j (κ z)) z)
      (λ x → refl)

Case : Type
Case = Actual.ShortCase

BA BC : Case → Type
BA c = τ₁ (Actual.A c)
BC c = τ₁ (Actual.C c)

private
  abstract
    exponent-nonzero : (c : Case) → ¬ pos (Actual.exponentOf c) ≡ pos 0
    exponent-nonzero Actual.octa h = snotz (cong abs h)
    exponent-nonzero Actual.icosa h = snotz (cong abs h)

abstract
  -- The all-points theorem is on the literal SAME Bundle.Mₑ as Actual.A.
  -- No connectedness argument, chosen sheet, or marked-basepoint transfer.
  κA-isEquiv : (c : Case) → isEquiv (κ {X = Actual.A c})
  κA-isEquiv c = κ-isEquiv-from-groupoid (Actual.A c)
    (trunc₂-groupoid-from-π₂ (Actual.A c)
      (Final.BundleAtEveryPoint.pi₂-zero
        (pos (Actual.exponentOf c)) (exponent-nonzero c)))

κA : (c : Case) → τ₂ (Actual.A c) ≃ BA c
κA c = κ , κA-isEquiv c
