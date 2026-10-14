{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Notation where

-- CW types, finite bounds, and homology notation; C 1 is the 0-skeleton.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Unit using (tt)
open import Cubical.CW.Base public using (CW ; isCW)
open import Cubical.CW.Base using
  (finCWskel ; finCWskel→CWskel ; realise ; isFinCW ; finCW→CW)
open import Cubical.CW.Homology.Base public using (H̃ᶜʷ ; H̃ᶜʷ→)
open import Cubical.CW.Instances.Pushout using (isPushoutᶜʷ)
open import Cubical.CW.Instances.Unit using (finCWUnit)
open import Cubical.HITs.Pushout.Base using (cofib)
import Cubical.HITs.PropositionalTruncation as PT

CW₀ : Type₁
CW₀ = CW ℓ-zero

Finite≤ : ℕ → Type → Type₁
Finite≤ d X = PT.∥ Σ[ C ∈ finCWskel ℓ-zero (suc d) ]
  (X ≃ realise (finCWskel→CWskel (suc d) C)) ∥₁

Hzero : CW₀ → ℕ → Type
Hzero X n = isContr (fst (H̃ᶜʷ X n))

Hiso : (A B : CW₀) → ℕ → (fst A → fst B) → Type
Hiso A B n f = isEquiv (fst (H̃ᶜʷ→ {C = A} {D = B} n f))

finite≤→isCW : {X : Type} {d : ℕ} → Finite≤ d X → isCW X
finite≤→isCW {d = d} = PT.map λ (C , e) →
  finCWskel→CWskel (suc d) C , e

finite≤→isFinCW : {X : Type} {d : ℕ} → Finite≤ d X → isFinCW X
finite≤→isFinCW {d = d} = PT.map λ (C , e) → suc d , C , e

-- Keep the large cellular-approximation witness opaque, while the
-- underlying HIT remains definitionally the actual cofibre.
private
  abstract
    cofib-isCW : (A B : CW₀) → isFinCW (fst A)
      → (f : fst A → fst B) → isCW (cofib f)
    cofib-isCW A B finA f =
      isPushoutᶜʷ (fst A , finA) (finCW→CW finCWUnit) B (λ _ → tt) f

cofibCW : (A B : CW₀) → isFinCW (fst A) → (fst A → fst B) → CW₀
cofibCW A B finA f = cofib f , cofib-isCW A B finA f
