{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Fracture.Pullback where

-- Finite change of the common pullback target.  The two comparison
-- homotopies are retained in the path component of the actual map.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lCancel)
open import Cubical.Foundations.Path using (compPathlEquiv ; compPathrEquiv)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (PB)

module ChangeApex (A B C D : Type) (k : C → D)
  (f : A → C) (g : B → C) (f' : A → D) (g' : B → D)
  (h : (a : A) → k (f a) ≡ f' a)
  (j : (b : B) → k (g b) ≡ g' b) where

  map : PB {A = A} {B = B} {C = C} f g
    → PB {A = A} {B = B} {C = D} f' g'
  map (a , b , p) = a , b , (sym (h a) ∙ cong k p) ∙ j b

  abstract
    map-isEquiv : isEquiv k → isEquiv map
    map-isEquiv ek = snd
      (Σ-cong-equiv-snd {A = A} λ a →
        Σ-cong-equiv-snd {A = B} λ b →
          compEquiv (congEquiv {x = f a} {y = g b} (k , ek))
            (compEquiv (compPathlEquiv (sym (h a))) (compPathrEquiv (j b))))

-- Both marked homotopies restrict to the SAME overlap β.  This identity
-- turns the image of the strict unit-square filler into refl, without
-- identifying arbitrary fillers or assuming that the target is a set.
abstract
  marked-refl : (D : Type) (x y : D) (p : x ≡ y)
    → (sym p ∙ refl) ∙ p ≡ refl
  marked-refl D x y p = cong (_∙ p) (sym (rUnit (sym p))) ∙ lCancel p
