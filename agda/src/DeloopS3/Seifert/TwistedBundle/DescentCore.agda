{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Generic path induction for descent. Keeping the families abstract
-- avoids unfolding EM group structure while checking transport equations.
module DeloopS3.Seifert.TwistedBundle.DescentCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

abstract
  evaluation-natural : ∀ {ℓX ℓY ℓZ ℓC}
    {X : Type ℓX} (Y : X → Type ℓY) (Z : X → Type ℓZ) {C : Type ℓC}
    (f : (x : X) → Y x → Z x → C)
    (s : X) {t : X} (p : s ≡ t) (y : Y t) (z : Z t)
    → f s (subst Y (sym p) y) (subst Z (sym p) z) ≡ f t y z
  evaluation-natural Y Z f s p = J {x = s}
    (λ t p → (y : Y t) (z : Z t)
      → f s (subst Y (sym p) y) (subst Z (sym p) z) ≡ f t y z)
    (λ y z → cong₂ (f s) (transportRefl y) (transportRefl z)) p

module SingletonTotal {ℓX ℓR ℓV : Level}
  {X : Type ℓX} {R : Type ℓR} (w : R → X) (V : X → Type ℓV) where

  Source : Type (ℓ-max ℓX (ℓ-max ℓR ℓV))
  Source = Σ X (λ t → (Σ R (λ x → w x ≡ t)) × V t)

  Target : Type (ℓ-max ℓR ℓV)
  Target = Σ R (λ x → V (w x))

  to : Source → Target
  to (t , (x , p) , v) = x , subst V (sym p) v

  from : Target → Source
  from (x , v) = w x , (x , refl) , v

  abstract
    sec : (z : Target) → to (from z) ≡ z
    sec (x , v) = ΣPathP (refl , transportRefl v)

    ret : (z : Source) → from (to z) ≡ z
    ret (t , (x , p) , v) = J {x = w x}
      (λ t p → (v : V t) → from (to (t , (x , p) , v)) ≡ (t , (x , p) , v))
      (λ v → cong {A = V (w x)} {B = λ _ → Source}
        (λ u → w x , (x , refl) , u) (transportRefl v)) p v

  equivalence : Source ≃ Target
  equivalence = isoToEquiv (iso to from sec ret)
