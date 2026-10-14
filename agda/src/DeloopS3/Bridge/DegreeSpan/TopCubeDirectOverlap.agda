{-# OPTIONS --cubical --safe #-}

module DeloopS3.Bridge.DegreeSpan.TopCubeDirectOverlap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (cong-∙; rCancel)
open import Cubical.HITs.Susp using (Susp; north; merid; suspFun)
open import DeloopS3.Bridge.DegreeSpan.TopCubeDirectCancellation
  using (cong-cancel-inverse-square)

module NormalizedNull {ℓ ℓ' : Level}
  (A : Type ℓ) (B : Type ℓ') (a : A) (f : A → B) where

  s : Susp A → Susp B
  s = suspFun f

  NS : A → Path (Susp A) north north
  NS z = merid z ∙ sym (merid a)

  NT : B → Path (Susp B) north north
  NT z = merid z ∙ sym (merid (f a))

  e : (z : A) → Path (Path (Susp B) north north)
    (cong s (NS z)) (NT (f z))
  e z = cong-∙ s (merid z) (sym (merid a))

  sourceBase : Path (Path (Susp A) north north) refl (NS a)
  sourceBase = sym (rCancel (merid a))

  targetBase : Path (Path (Susp B) north north) refl (NT (f a))
  targetBase = sym (rCancel (merid (f a)))

  nullS : {z : A} (q : a ≡ z) →
    Path (Path (Susp A) north north) refl (NS z)
  nullS q = sourceBase ∙ cong NS q

  nullT : {z : A} (q : a ≡ z) →
    Path (Path (Susp B) north north) refl (NT (f z))
  nullT q = targetBase ∙ cong (NT ∘ f) q

  abstract
    base-square : Square {A = Path (Susp B) north north}
      (cong (cong s) sourceBase) targetBase refl (e a)
    base-square = cong-cancel-inverse-square s (merid a)

    meridian-square : {z : A} (q : a ≡ z) →
      Square {A = Path (Susp B) north north}
        (cong (cong s ∘ NS) q) (cong (NT ∘ f) q) (e a) (e z)
    meridian-square q t j = e (q j) t

    null-square : {z : A} (q : a ≡ z) →
      Square {A = Path (Susp B) north north}
        (cong (cong s) (nullS q)) (nullT q) refl (e z)
    null-square q =
      cong-∙ (cong s) sourceBase (cong NS q)
        ◁ (λ t → base-square t ∙ meridian-square q t)
