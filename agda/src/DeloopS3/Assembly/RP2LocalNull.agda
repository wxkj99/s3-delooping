{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Degree-2 circle localization contracts RP 2 via its degree-2 cofibre
-- presentation, not the library's separate small RP² HIT.
module DeloopS3.Assembly.RP2LocalNull where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua; pathToEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base using (Pushout; cofib; symPushout)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)

open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
open import DeloopS3.Local.Base
  using (L; LocalEquiv; deg₁; powLoop; local→preEquiv)
open import DeloopS3.Local.Powers using (cong-powLoop)
open import DeloopS3.Local.Kernel using (local-cofib-contr)
import DeloopS3.Seifert.TwistedBundle.Base as B
import DeloopS3.Seifert.TwistedBundle.Chart as Ch
import DeloopS3.Seifert.MarkedSeifert.DescentChart as D

-- These charts retain the positive two-edge/four-edge generators. Thus
-- w-projects fixes the sign as +2; Base.fA and its unmarked sign are unused.
abstract
  covering-circle-loop :
    cong (B.pr₁ ∘ D.aCircle₀) loop
      ≡ cong (D.rCircle ∘ deg₁ 2) loop
  covering-circle-loop = Ch.w-projects ∙ sym
    (cong-powLoop D.rCircle 2 loop
      ∙ cong (Ch.t ∙_) (sym (rUnit Ch.t)))

covering-circle-square :
  B.pr₁ ∘ D.aCircle₀ ≡ D.rCircle ∘ deg₁ 2
covering-circle-square = funExt λ
  { base → refl
  ; (loop i) → λ j → covering-circle-loop j i }

covering-circle-square-base :
  funExt⁻ covering-circle-square base ≡ refl
covering-circle-square-base = refl

private
  circle-cap : S¹ → Unit
  circle-cap _ = tt

abstract
  -- The source is the circle presentation with RP's vertex order.
  -- The target reduces to the defining pushout of RP 2.
  circle-span≃RP² : Pushout (deg₁ 2) circle-cap ≃ RP²
  circle-span≃RP² = pushoutEquiv
    {A₁ = S¹} {B₁ = S¹} {C₁ = Unit}
    {A₂ = B.A} {B₂ = B.R} {C₂ = Unit}
    (deg₁ 2) circle-cap B.pr₁ B.cap
    (D.aCircle₀ , D.aCircle₀-isEquiv)
    (D.rCircle , D.rCircle-isEquiv) (idEquiv Unit)
    (sym covering-circle-square) refl

  RP²≃cofib-double : RP² ≃ cofib (deg₁ 2)
  RP²≃cofib-double = compEquiv
    {A = RP²} {B = Pushout (deg₁ 2) circle-cap}
    {C = cofib (deg₁ 2)}
    (invEquiv circle-span≃RP²) (symPushout (deg₁ 2) circle-cap)

  -- Only an equivalence of localized TYPES is needed for contractibility.
  -- This univalence construction is independent of the specified L-map
  -- and makes no claim about the latter's unit/naturality computations.
  L-respect-equiv : (m : ℕ) {X Y : Type ℓ-zero}
    → X ≃ Y → L m X ≃ L m Y
  L-respect-equiv m e = pathToEquiv (cong (L m) (ua e))

  L-contr-respect-equiv : (m : ℕ) {X Y : Type ℓ-zero}
    → X ≃ Y → isContr (L m X) → isContr (L m Y)
  L-contr-respect-equiv m {X} {Y} e = isOfHLevelRespectEquiv 0
    (L-respect-equiv m {X = X} {Y = Y} e)

  -- Locality is precisely invertibility of precomposition by deg₁ m.
  degree-local-equiv : (m : ℕ) → LocalEquiv m (deg₁ m)
  degree-local-equiv m Z localZ = local→preEquiv {m = m} {X = Z} localZ

  cofib-double-local₂-contr : isContr (L 2 (cofib (deg₁ 2)))
  cofib-double-local₂-contr = local-cofib-contr
    {m = 2} {A = S¹} {B = S¹} (deg₁ 2) (degree-local-equiv 2)

  RP²-local-contr-from-cofib : (m : ℕ)
    → isContr (L m (cofib (deg₁ 2))) → isContr (L m RP²)
  RP²-local-contr-from-cofib m = L-contr-respect-equiv m
    {X = cofib (deg₁ 2)} {Y = RP²} (invEquiv RP²≃cofib-double)

  RP²-local₂-contr : isContr (L 2 RP²)
  RP²-local₂-contr = RP²-local-contr-from-cofib 2 cofib-double-local₂-contr
