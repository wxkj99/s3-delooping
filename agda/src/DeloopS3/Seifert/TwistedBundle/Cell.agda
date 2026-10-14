{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The small circle family over RP², descended from the coherent action,
-- with its projection, cap fibre and truncation-unit pullback square.
module DeloopS3.Seifert.TwistedBundle.Cell where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Int using (ℤ)
open import Cubical.HITs.RPn.Base using (Bool*)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Fibration using (fiberEquiv)
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Coherent
open import DeloopS3.Sphere.RP2UnitFiber using (RP²; rpBase; RP²-unit-fiber)
open import DeloopS3.Sphere.TruncationCartesian
open import Cubical.HITs.S3 using (S³)

module Bundle (e : ℤ) where
  open Action e
  open Descended e

  Fₑ : RP² → Type
  Fₑ = Fdescent

  Mₑ : Type
  Mₑ = Mdescent

  pₑ : Mₑ → RP²
  pₑ = fst

  actionFamily : QuotientBase → Type
  actionFamily (T , s) = FAct T s

  capLift : QuotientBase
  capLift = Bool* , inr false

  -- The inverse-law basepoint path is retained; it is not reset to refl.
  capFrame : Fₑ (inr tt) ≃ C
  capFrame = compEquiv
    (pathToEquiv (cong actionFamily (cong (invEq baseQuotient) (sym baseQuotient-cap) ∙ retEq baseQuotient capLift)))
    (ε Bool* false)

  m₀ : Mₑ
  m₀ = inr tt , invEq capFrame 0C

  family-circle : (b : RP²) → PT.∥ Fₑ b ≃ C ∥₁
  family-circle = descent-circle

  family-groupoid : (b : RP²) → isGroupoid (Fₑ b)
  family-groupoid b = PT.rec isPropIsGroupoid
    (λ eq → isOfHLevelRetractFromIso 3 (equivToIso eq) emsquash)
    (family-circle b)

  projection-fibre : (b : RP²) → fiber pₑ b ≃ Fₑ b
  projection-fibre = fiberEquiv Fₑ

  circleFibres : (b : RP²) → PT.∥ fiber pₑ b ≃ C ∥₁
  circleFibres b = PT.map (compEquiv (projection-fibre b)) (family-circle b)

  baseFibre : fiber pₑ (inr tt) ≃ C
  baseFibre = compEquiv (projection-fibre (inr tt)) capFrame

  baseFibre-point : baseFibre .fst (m₀ , refl) ≡ 0C
  baseFibre-point = cong (capFrame .fst) (transportRefl (invEq capFrame 0C))
    ∙ secEq capFrame 0C

  fibre-groupoid : (b : RP²) → isGroupoid (fiber pₑ b)
  fibre-groupoid b = isOfHLevelRetractFromIso 3
    (equivToIso (projection-fibre b)) (family-groupoid b)

  truncation-cartesian : CartSquare pₑ (τ₂-map pₑ) η₂ η₂
    (trunc₂-naturality pₑ)
  truncation-cartesian = trunc₂-cartesian pₑ fibre-groupoid

  bundle-unit-fibres : (z : τ₂ Mₑ)
    → fiber η₂ z ≃ fiber η₂ (τ₂-map pₑ z)
  bundle-unit-fibres = trunc₂-unit-fibers pₑ fibre-groupoid

  total-unit-fibre : (m : Mₑ) → pₑ m ≡ rpBase
    → fiber (η₂ {A = Mₑ}) (η₂ m) ≃ S³
  total-unit-fibre m h = compEquiv (bundle-unit-fibres (η₂ m))
    (compEquiv (pathToEquiv (cong (λ b → fiber (η₂ {A = RP²}) (η₂ b)) h))
      RP²-unit-fiber)

-- The family uses coherent descent rather than a direct cell recursor.
-- MarkedSeifert.Final.SmallSpan compares its total space with the small pushout.
