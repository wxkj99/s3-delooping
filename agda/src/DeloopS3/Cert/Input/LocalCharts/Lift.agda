{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Lift where

open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT

-- Existence uses the specified based lift, not just
-- faithfulness of path projection. The dependent path type is a prop.
abstract
  based-lift-unique : {B X : Type₀} (F : B → Type₀)
    → ((b : B) → isSet (F b)) → (x₀ : X)
    → ((x : X) → PT.∥ x₀ ≡ x ∥₁)
    → (f g : X → Σ B F)
    → (h : (x : X) → fst (f x) ≡ fst (g x))
    → (p : f x₀ ≡ g x₀) → cong fst p ≡ h x₀
    → Σ[ H ∈ ((x : X) → f x ≡ g x) ]
        ((x : X) → cong fst (H x) ≡ h x)
  based-lift-unique {X = X} F setF x₀ connected f g h p over =
    (λ x i → h x i , lift x i) , (λ x → refl)
    where
    D : X → Type₀
    D x = PathP (λ i → F (h x i)) (f x .snd) (g x .snd)
    propD : (x : X) → isProp (D x)
    propD x = isOfHLevelPathP' 1 (setF (g x .fst)) _ _
    at-base : D x₀
    at-base = subst (λ q → PathP (λ i → F (q i)) (f x₀ .snd) (g x₀ .snd))
      over (λ i → p i .snd)
    lift : (x : X) → D x
    lift x = PT.rec (propD x) (λ q → subst D q at-base) (connected x)
