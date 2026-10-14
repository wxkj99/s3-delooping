{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import DeloopS3.Bridge.SeifertChains.Matrices

-- Keep dependent coordinate fields on arbitrary groups. Instantiating
-- their record elaboration directly at H̃ᶜʷ expands cellular approximation.
record H1CoordinateData (HA₁ HV₁ HA₀ HV₀ : Group₀)
  (s₁ : fst HA₁ → fst HV₁) (s₀ : fst HA₀ → fst HV₀) (q n : ℤ) : Type₀ where
  field
    overlap-coordinates : GroupEquiv HA₁ (AbGroup→Group ℤ⁶)
    vertices : GroupEquiv HV₁ (AbGroup→Group vertex₁)
    matrix-square : (a : fst HA₁)
      → fst (Araw (pos 2) q n) (equivFun (fst overlap-coordinates) a)
        ≡ equivFun (fst vertices) (s₁ a)
    zero-tail : (a : fst HA₀) → s₀ a ≡ GroupStr.1g (snd HV₀)
      → a ≡ GroupStr.1g (snd HA₀)
