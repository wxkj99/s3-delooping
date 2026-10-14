{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Complete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv ; isSurjective)
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (Hzero)
open import DeloopS3.Cert.Interpret.Short using (ShortCase ; octa ; icosa)
open import DeloopS3.Bridge.Profile.BaseSeifert.HurewiczProductMarkings
  using (hurewicz-chart-identification)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns using (BoundaryColumns)
open import DeloopS3.Bridge.Profile.H1Data.Components
  using (ComponentH1Inputs ; ComponentH1Groups)
open import DeloopS3.Bridge.Profile.H1Data.Actual
  using (ACW ; CCW ; outer-H₁-map ; outer-H₁-onto)
open import DeloopS3.Bridge.Profile.H1Data.OuterAlgebra using (C₂)
open import DeloopS3.Bridge.Profile.H1Data.OuterConsequences
  using (outer-O-isEquiv-from-inner ; outer-I-kernel-from-inner)
import DeloopS3.Bridge.Profile.ComponentInputs as Inputs

-- HurewiczProductMarkings supplies the chart identification. ComponentInputs
-- transports CW witnesses and H₀ tails for the component and outer-map calculations.
abstract
  component-inputs : ComponentH1Inputs
  component-inputs = Inputs.component-H₁-inputs hurewicz-chart-identification

  component-groups : PT.∥ ComponentH1Groups ∥₁
  component-groups = Inputs.component-H₁-groups hurewicz-chart-identification

  -- These endpoints are the ACTUAL signed map (q_*,-p_*) on the literal
  -- original components, not a map chosen in finite-group coordinates.
  outer-O-isEquiv : isEquiv (fst (outer-H₁-map octa))
  outer-O-isEquiv = outer-O-isEquiv-from-inner component-inputs

  outer-I-kernel : PT.∥ GroupEquiv (kerGroup (outer-H₁-map icosa)) C₂ ∥₁
  outer-I-kernel = outer-I-kernel-from-inner component-inputs

  outer-I-onto : isSurjective (outer-H₁-map icosa)
  outer-I-onto = outer-H₁-onto icosa

  -- Boundary columns give H₂ vanishing at the H1Data.Actual.ACW/CCW endpoints,
  -- without an H₃ coordinate choice.
  source-H₂-zero : BoundaryColumns → (c : ShortCase) → Hzero (ACW c) 2
  source-H₂-zero = Inputs.source-H₂-zero hurewicz-chart-identification

  target-H₂-zero : BoundaryColumns → (c : ShortCase) → Hzero (CCW c) 2
  target-H₂-zero = Inputs.target-H₂-zero hurewicz-chart-identification
