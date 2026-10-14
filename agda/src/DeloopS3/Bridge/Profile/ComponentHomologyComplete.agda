{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.ComponentHomologyComplete where

-- Homology of the actual source and target components. Group-equivalence
-- choices remain propositionally truncated, independently of cover-map compatibility.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; invEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupEquiv)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
open import DeloopS3.Bridge.Profile.H1Data.Actual using (ACW ; CCW)
open import DeloopS3.Bridge.Profile.H1Data.Components using (ComponentH1Groups)
open import DeloopS3.Bridge.Profile.BaseSeifert.HurewiczProductMarkings using
  (hurewicz-chart-identification)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns using
  (boundary-columns→degree-two)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFinal using
  (base-seifert-boundary-columns)
import DeloopS3.Bridge.Profile.BaseSeifert.Cases as Cases
import DeloopS3.Bridge.Profile.ComponentInputs as Inputs

-- Seal transports while the groups and CW witnesses are still variables.
-- No truncation is eliminated into an untruncated group-equivalence choice.
private
  abstract
    compose-group-choice : (G H K : Group₀) → GroupEquiv G H
      → PT.∥ GroupEquiv H K ∥₁ → PT.∥ GroupEquiv G K ∥₁
    compose-group-choice G H K e = PT.map (compGroupEquiv e)

    pullback-homology-choice : (X Y : CW₀) (n : ℕ)
      → fst X ≃ fst Y → (G : Group₀)
      → PT.∥ GroupEquiv (H̃ᶜʷ Y n) G ∥₁
      → PT.∥ GroupEquiv (H̃ᶜʷ X n) G ∥₁
    pullback-homology-choice X Y n e G =
      compose-group-choice (H̃ᶜʷ X n) (H̃ᶜʷ Y n) G
        (H̃ᶜʷ→Equiv {C = X} {D = Y} n e)

    pullback-homology-zero : (X Y : CW₀) (n : ℕ)
      → fst X ≃ fst Y → Hzero Y n → Hzero X n
    pullback-homology-zero X Y n e = isOfHLevelRespectEquiv 0
      (invEquiv (fst (H̃ᶜʷ→Equiv {C = X} {D = Y} n e)))

abstract
  component-H₁-groups : PT.∥ ComponentH1Groups ∥₁
  component-H₁-groups = Inputs.component-H₁-groups hurewicz-chart-identification

  source-H₂-zero : (c : ShortCase) → Hzero (ACW c) 2
  source-H₂-zero = Inputs.source-H₂-zero
    hurewicz-chart-identification base-seifert-boundary-columns

  target-H₂-zero : (c : ShortCase) → Hzero (CCW c) 2
  target-H₂-zero = Inputs.target-H₂-zero
    hurewicz-chart-identification base-seifert-boundary-columns

  -- The underlying spaces are definitionally equal; their CW witnesses
  -- need not be. Transport is along the homology equivalence of idEquiv.
  source-H₃ : (c : ShortCase) → PT.∥ GroupEquiv (H̃ᶜʷ (ACW c) 3) ℤGroup ∥₁
  source-H₃ c = pullback-homology-choice (ACW c) (Cases.sourceCW c) 3
    (idEquiv (fst (ACW c))) ℤGroup
    (Cases.source-H₃-from-D c
      (boundary-columns→degree-two base-seifert-boundary-columns
        (pos 2) (pos 2) (Cases.source-r c)))

  target-H₃ : (c : ShortCase) → PT.∥ GroupEquiv (H̃ᶜʷ (CCW c) 3) ℤGroup ∥₁
  target-H₃ c = pullback-homology-choice (CCW c) (Cases.baseCW c) 3
    (idEquiv (fst (CCW c))) ℤGroup
    (Cases.base-H₃-from-D c
      (boundary-columns→degree-two base-seifert-boundary-columns
        (pos 2) (pos 3) (Cases.base-r c)))

  source-H₄-zero : (c : ShortCase) → Hzero (ACW c) 4
  source-H₄-zero c = pullback-homology-zero (ACW c) (Cases.sourceCW c) 4
    (idEquiv (fst (ACW c))) (Cases.source-H₄-zero c)

  target-H₄-zero : (c : ShortCase) → Hzero (CCW c) 4
  target-H₄-zero c = pullback-homology-zero (CCW c) (Cases.baseCW c) 4
    (idEquiv (fst (CCW c))) (Cases.base-H₄-zero c)
