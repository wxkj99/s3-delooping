{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The bundle's connecting homomorphism and π₂-vanishing criteria from
-- an injective boundary, a nonzero integer coordinate, or a fibre relation.
module DeloopS3.Seifert.TwistedBundle.Pi2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Int using (ℤ; pos; _·_)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (GroupEquiv→GroupHom; compGroupHom; makeIsGroupHom; invGroupEquiv; compGroupEquiv)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash; emloop-comp)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (ΩEM₁Iso)
open import Cubical.Homotopy.Group.Base using (π; πGr; πIso)
import Cubical.HITs.SetTruncation as ST
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Exactness

module Homotopy (e : ℤ) where
  open Bundle e

  projection∙ : (Mₑ , m₀) →∙ (RP² , inr tt)
  projection∙ = pₑ , refl

  module S = Sequence projection∙

  capFrame∙ : S.LES.fib ≃∙ (C , 0C)
  capFrame∙ = baseFibre , baseFibre-point

  connectingHom : GroupHom (πGr 1 (RP² , inr tt)) (πGr 0 (C , 0C))
  connectingHom = compGroupHom S.connecting
    (GroupEquiv→GroupHom (πIso capFrame∙ 0))

  circleIntegerChart : π 1 (C , 0C) ≃ ℤ
  circleIntegerChart = isoToEquiv
    (compIso (ST.setTruncIdempotentIso (emsquash 0C 0C)) (ΩEM₁Iso ℤGroup))

  fibreIntegerChart : π 1 S.LES.fib ≃ ℤ
  fibreIntegerChart = compEquiv (πIso capFrame∙ 0 .fst) circleIntegerChart

  connectingℤ : π 2 (RP² , inr tt) → ℤ
  connectingℤ x = fibreIntegerChart .fst (S.connecting .fst x)

  pi₂-cap-fibre-zero : isContr (π 2 S.LES.fib)
  pi₂-cap-fibre-zero = pi₂-groupoid-zero (fibre-groupoid (inr tt)) (m₀ , refl)

  pi₂-zero-from-injective-boundary :
    ((x y : π 2 (RP² , inr tt))
      → S.connecting .fst x ≡ S.connecting .fst y → x ≡ y)
    → isContr (π 2 (Mₑ , m₀))
  pi₂-zero-from-injective-boundary =
    S.vanishing-from-injective-boundary pi₂-cap-fibre-zero

  pi₂-zero-from-boundary-coordinate : (d : ℤ) → ¬ d ≡ pos 0
    → (chart : π 2 (RP² , inr tt) ≃ ℤ)
    → ((x : π 2 (RP² , inr tt)) → connectingℤ x ≡ d · chart .fst x)
    → isContr (π 2 (Mₑ , m₀))
  pi₂-zero-from-boundary-coordinate d nz chart computation =
    S.vanishing-from-integer-coordinate pi₂-cap-fibre-zero d nz
      chart fibreIntegerChart computation

  pi₂-zero-from-twice-e : ¬ e ≡ pos 0
    → (chart : π 2 (RP² , inr tt) ≃ ℤ)
    → ((x : π 2 (RP² , inr tt)) → connectingℤ x ≡ (pos 2 · e) · chart .fst x)
    → isContr (π 2 (Mₑ , m₀))
  pi₂-zero-from-twice-e nz = pi₂-zero-from-boundary-coordinate
    (pos 2 · e) (twice-nonzero e nz)

  -- The fibre-relation criterion uses group charts, not only carrier equivalences.
  integerCircleGroup : GroupEquiv ℤGroup (πGr 0 (C , 0C))
  integerCircleGroup .fst = invEquiv circleIntegerChart
  integerCircleGroup .snd = makeIsGroupHom λ n m →
    cong ST.∣_∣₂ (emloop-comp ℤGroup n m)

  fibreIntegerGroup : GroupEquiv (πGr 0 S.LES.fib) ℤGroup
  fibreIntegerGroup = compGroupEquiv (πIso capFrame∙ 0) (invGroupEquiv integerCircleGroup)

  fibreElement : ℤ → π 1 S.LES.fib
  fibreElement = invEq (fibreIntegerGroup .fst)

  pi₂-zero-from-power-relation : ¬ e ≡ pos 0
    → GroupEquiv (πGr 1 (RP² , inr tt)) ℤGroup
    → isInKer (S.LES.fib→A 0) (fibreElement (pos 2 · e))
    → isContr (π 2 (Mₑ , m₀))
  pi₂-zero-from-power-relation nz baseChart relation =
    S.vanishing-from-fibre-relation pi₂-cap-fibre-zero baseChart fibreIntegerGroup
      (fibreElement (pos 2 · e))
      (λ h → twice-nonzero e nz (sym (secEq (fibreIntegerGroup .fst) (pos 2 · e)) ∙ h))
      relation

-- Pi2Zero proves π₂(Mₑ) = 0 for e ≠ 0 using TwoCap's suspension model
-- and a nonzero image, without a signed coordinate formula for this boundary.
