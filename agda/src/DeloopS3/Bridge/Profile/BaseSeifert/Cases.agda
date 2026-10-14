{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Cases where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroupStr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim using (CW₀ ; Hzero)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ⁶ ; vertex₁ ; Araw ; Araw-kernel)
open import DeloopS3.Bridge.SeifertChains.Seifert using (positive-cancel)
open import DeloopS3.Bridge.SeifertChains.Cases using (Araw-octa-kernel ; Araw-icosa-kernel)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry
open import DeloopS3.Bridge.Profile.BaseSeifert.Reduction
open import DeloopS3.Cert.Input.Model.Vocabulary using (ShortCase ; octa ; icosa)
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Check as Check
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Bridge.OriginalSpan as Original

base-r source-r : ShortCase → ℤ
base-r c = pos (Input.localOrder c Check.C)
source-r c = pos (Short.exponentOf c)

baseCW sourceCW : ShortCase → CW₀
baseCW c = seifertCW (pos 2) (pos 3) (base-r c)
sourceCW c = seifertCW (pos 2) (pos 2) (source-r c)

-- Definitional endpoint equalities, including Input.M-original itself.
base-endpoint : (c : ShortCase) → fst (baseCW c) ≡ Input.M-original c
base-endpoint c = refl

C-endpoint : (c : ShortCase) → fst (baseCW c) ≡ Original.C c
C-endpoint c = refl

A-endpoint : (c : ShortCase) → fst (sourceCW c) ≡ Original.A c
A-endpoint c = refl

abstract
  base-H₄-zero : (c : ShortCase) → Hzero (baseCW c) 4
  base-H₄-zero c = seifert-H₄-zero (pos 2) (pos 3) (base-r c)

  source-H₄-zero : (c : ShortCase) → Hzero (sourceCW c) 4
  source-H₄-zero c = seifert-H₄-zero (pos 2) (pos 2) (source-r c)

  base-H₃-kernel : (c : ShortCase)
    → PT.∥ GroupEquiv (H̃ᶜʷ (baseCW c) 3)
        (kerGroup (seifert-source (pos 2) (pos 3) (base-r c) 1)) ∥₁
  base-H₃-kernel c = seifert-H₃-kernel (pos 2) (pos 3) (base-r c)

  source-H₃-kernel : (c : ShortCase)
    → PT.∥ GroupEquiv (H̃ᶜʷ (sourceCW c) 3)
        (kerGroup (seifert-source (pos 2) (pos 2) (source-r c) 1)) ∥₁
  source-H₃-kernel c = seifert-H₃-kernel (pos 2) (pos 2) (source-r c)

  base-H₃-from-D : (c : ShortCase)
    → DegreeTwoComparison (pos 2) (pos 3) (base-r c)
    → PT.∥ GroupEquiv (H̃ᶜʷ (baseCW c) 3) ℤGroup ∥₁
  base-H₃-from-D c = WithDegreeTwo.H₃-integers (pos 2) (pos 3) (base-r c)

  source-H₃-from-D : (c : ShortCase)
    → DegreeTwoComparison (pos 2) (pos 2) (source-r c)
    → PT.∥ GroupEquiv (H̃ᶜʷ (sourceCW c) 3) ℤGroup ∥₁
  source-H₃-from-D c = WithDegreeTwo.H₃-integers (pos 2) (pos 2) (source-r c)

private
  base-kernel : (c : ShortCase) (a : fst ℤ⁶)
    → fst (Araw (pos 2) (pos 3) (base-r c)) a ≡ AbGroupStr.0g (snd vertex₁)
    → a ≡ AbGroupStr.0g (snd ℤ⁶)
  base-kernel octa = Araw-octa-kernel
  base-kernel icosa = Araw-icosa-kernel

  source-kernel : (c : ShortCase) (a : fst ℤ⁶)
    → fst (Araw (pos 2) (pos 2) (source-r c)) a ≡ AbGroupStr.0g (snd vertex₁)
    → a ≡ AbGroupStr.0g (snd ℤ⁶)
  source-kernel octa = Araw-kernel (pos 2) (pos 2) (pos 4) (positive-cancel 1) (positive-cancel 3)
  source-kernel icosa = Araw-kernel (pos 2) (pos 2) (pos 3) (positive-cancel 1) (positive-cancel 3)

abstract
  base-H₂-from-matrices : (c : ShortCase)
    → DegreeTwoComparison (pos 2) (pos 3) (base-r c)
    → DegreeOneComparison (pos 2) (pos 3) (base-r c)
    → Hzero (baseCW c) 2
  base-H₂-from-matrices c d₂ d₁ = WithDegreeTwo.H₂-from-degree-one
    (pos 2) (pos 3) (base-r c) d₂ d₁ (base-kernel c)

  source-H₂-from-matrices : (c : ShortCase)
    → DegreeTwoComparison (pos 2) (pos 2) (source-r c)
    → DegreeOneComparison (pos 2) (pos 2) (source-r c)
    → Hzero (sourceCW c) 2
  source-H₂-from-matrices c d₂ d₁ = WithDegreeTwo.H₂-from-degree-one
    (pos 2) (pos 2) (source-r c) d₂ d₁ (source-kernel c)
