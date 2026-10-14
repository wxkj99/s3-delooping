{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.PiecesH2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv)
open import DeloopS3.Cert.Interpret.Short using (ShortCase ; octa ; icosa)
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.SeifertChains.Matrices using (Araw ; Araw-kernel)
open import DeloopS3.Bridge.SeifertChains.Seifert using (positive-cancel)
open import DeloopS3.Bridge.SeifertChains.Cases using (Araw-octa-kernel ; Araw-icosa-kernel)
open import DeloopS3.Bridge.Profile.H1Data.Actual using (ACW ; CCW)
open import DeloopS3.Bridge.Profile.H1Data.Components
open import DeloopS3.Bridge.Profile.H1Data.InnerH2

module SO₂ = ForInner (pos 2) (pos 4)
module SI₂ = ForInner (pos 2) (pos 3)
module TO₂ = ForInner (pos 3) (pos 4)
module TI₂ = ForInner (pos 3) (pos 5)

-- Four source-map surjectivity inputs, rather than assumed homology vanishings.
ComponentH2Inputs : Type₀
ComponentH2Inputs = FourInputs SO₂.H2SourceOnto SI₂.H2SourceOnto TO₂.H2SourceOnto TI₂.H2SourceOnto
module ComponentH2Inputs = FourInputs

abstract
  pullback-H₂-zero : (X Y : CW₀) → fst X ≃ fst Y → Hzero Y 2 → Hzero X 2
  pullback-H₂-zero X Y e = isOfHLevelRespectEquiv 0
    (invEquiv (fst (H̃ᶜʷ→Equiv {C = X} {D = Y} 2 e)))

  source-H₂-zero-from-inner : ComponentH1Inputs → ComponentH2Inputs
    → (c : ShortCase) → Hzero (ACW c) 2
  source-H₂-zero-from-inner h₁ h₂ octa = pullback-H₂-zero (ACW octa) SourceO.totalCW (idEquiv _)
    (SO₂.H₂-from-inner-MV (ComponentH1Inputs.source-O h₁)
      (Araw-kernel (pos 2) (pos 2) (pos 4) (positive-cancel 1) (positive-cancel 3))
      (ComponentH2Inputs.source-O h₂))
  source-H₂-zero-from-inner h₁ h₂ icosa = pullback-H₂-zero (ACW icosa) SourceI.totalCW (idEquiv _)
    (SI₂.H₂-from-inner-MV (ComponentH1Inputs.source-I h₁)
      (Araw-kernel (pos 2) (pos 2) (pos 3) (positive-cancel 1) (positive-cancel 3))
      (ComponentH2Inputs.source-I h₂))

  target-H₂-zero-from-inner : ComponentH1Inputs → ComponentH2Inputs
    → (c : ShortCase) → Hzero (CCW c) 2
  target-H₂-zero-from-inner h₁ h₂ octa = pullback-H₂-zero (CCW octa) TargetO.totalCW (idEquiv _)
    (TO₂.H₂-from-inner-MV (ComponentH1Inputs.target-O h₁) Araw-octa-kernel (ComponentH2Inputs.target-O h₂))
  target-H₂-zero-from-inner h₁ h₂ icosa = pullback-H₂-zero (CCW icosa) TargetI.totalCW (idEquiv _)
    (TI₂.H₂-from-inner-MV (ComponentH1Inputs.target-I h₁) Araw-icosa-kernel (ComponentH2Inputs.target-I h₂))
