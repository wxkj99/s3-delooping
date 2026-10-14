{-# OPTIONS --cubical --safe #-}

module DeloopS3.Bridge.DegreeSpan.TopCubeDirectCancellation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

abstract
  cong-rCancel-square :
    ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A}
    (f : A → B) (p : x ≡ y) →
    Square {A = Path B (f x) (f x)}
      (cong (cong f) (rCancel p))
      (rCancel (cong f p))
      (cong-∙ f p (sym p))
      refl
  cong-rCancel-square {x = x} f p t j i =
    hcomp
      (λ k → λ
        { (t = i0) → f (rCancel-filler p k j i)
        ; (t = i1) → rCancel-filler (cong f p) k j i
        ; (j = i0) → cong-∙∙-filler f refl p (sym p) k t i
        ; (j = i1) → f x
        ; (i = i0) → f x
        ; (i = i1) → f (p (~ k ∧ ~ j))
        })
      (f (p (i ∧ ~ j)))

  cong-cancel-inverse-square :
    ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A}
    (f : A → B) (p : x ≡ y) →
    Square {A = Path B (f x) (f x)}
      (cong (cong f) (sym (rCancel p)))
      (sym (rCancel (cong f p)))
      refl
      (cong-∙ f p (sym p))
  cong-cancel-inverse-square f p t j = cong-rCancel-square f p t (~ j)
