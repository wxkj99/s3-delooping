{-# OPTIONS --safe --cubical #-}

-- Marked first-two-fillings interface, retaining the third torus boundary.
-- WRelJR constructs WComparison for M22e.
module DeloopS3.Seifert.MarkedSeifert.WInterface where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos; _-_)
open import Cubical.HITs.Pushout.Base
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC; _+C_)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)

row : ℤ → ℤ → T² → C
row s n (a , t) = mulC s a +C mulC n t

W : Type₀
W = Pushout (mulC (pos 2)) (mulC (pos 2))

-- Untruncated presentation after the two R1 cancellations, before torus filling.
data RelJR : Type₀ where
  vertex : RelJR
  j r : vertex ≡ vertex
  relation : j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r)

record WComparison (M22e : ℤ → Type₀) : Type₁ where
  field
    bW : T² → W
    W≃RelJR : W ≃ RelJR
    thirdStaged : (e : ℤ) → M22e e ≃ Pushout bW (row (pos 1 - e) e)

  bJR : T² → RelJR
  bJR t = W≃RelJR .fst (bW t)

  field
    boundary-base : bJR (0C , 0C) ≡ vertex
    boundary-u : (sym boundary-base ∙ cong bJR (λ i → hC i , 0C)) ∙ boundary-base
      ≡ sym (j ∙ (j ∙ sym r))
    boundary-v : (sym boundary-base ∙ cong bJR (λ i → 0C , hC i)) ∙ boundary-base
      ≡ j ∙ j
