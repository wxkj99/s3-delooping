{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Assembly.ConnectivityGlue.Surjectivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as T
import DeloopS3.Assembly.ActualSpans as Actual
import DeloopS3.Assembly.LocalCubes as LC
open import DeloopS3.Assembly.Final.Geometry using (ShortCase; R; N; E; P; p)

-- Only the vertex formulas for the ACTUAL mixed-cube map are used.
-- The seam is filled in a proposition, so no formula for its composite
-- homotopy (and no expansion of the cartesianness proofs) is needed.
module At (c : ShortCase) where
  private
    Preimage : P c → Type
    Preimage z = PT.∥ fiber (p c) z ∥₁

    left : (n : N) → Preimage (inl n)
    left = T.elim {A = R} {n = 4}
      {B = λ n → Preimage (inl n)}
      (λ _ → isProp→isOfHLevelSuc 3 PT.squash₁)
      (λ r → PT.∣ inl r , refl ∣₁)

    right : (z : LC.BC c) → Preimage (inr z)
    right = T.elim {A = Actual.C c} {n = 3}
      {B = λ z → Preimage (inr z)}
      (λ _ → isProp→isOfHLevelSuc 2 PT.squash₁)
      (λ z → PT.∣ inr z , refl ∣₁)

  -- Keep this proof outside an abstract block: checking its constructors
  -- needs only the transparent vertex equations of LocalCube.D.t.
  surjective : (z : P c) → PT.∥ fiber (p c) z ∥₁
  surjective (inl n) = left n
  surjective (inr z) = right z
  surjective (push a i) = isProp→PathP
    {B = λ j → Preimage (push a j)} (λ _ → PT.squash₁)
    (left (LC.qbar c a)) (right (LC.pbar c a)) i

abstract
  t-surjective : (c : ShortCase) (z : P c) → PT.∥ fiber (p c) z ∥₁
  t-surjective = At.surjective
