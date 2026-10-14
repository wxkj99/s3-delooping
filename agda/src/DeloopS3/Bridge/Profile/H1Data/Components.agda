{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Components where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Cert.Interpret.Short using (octa ; icosa)
open import DeloopS3.Bridge.Profile.H1Data.Actual using (ACW ; CCW ; RCW)
open import DeloopS3.Bridge.Profile.H1Data.Inner
open import DeloopS3.Bridge.Profile.H1Data.Cases
open import DeloopS3.Bridge.ComponentHomology.RP2 using (RP²-H₁ ; RP²-H₂)

module SourceO = Inner (pos 2) (pos 4)
module SourceI = Inner (pos 2) (pos 3)
module TargetO = Inner (pos 3) (pos 4)
module TargetI = Inner (pos 3) (pos 5)

abstract
  change-CW-H₁ : (X Y : CW₀) → fst X ≃ fst Y → GroupEquiv (H̃ᶜʷ X 1) (H̃ᶜʷ Y 1)
  change-CW-H₁ X Y = H̃ᶜʷ→Equiv {C = X} {D = Y} 1

  R-H₁ : GroupEquiv (H̃ᶜʷ RCW 1) (ℤGroup/ 2)
  R-H₁ = RP²-H₁

  R-H₂-zero : Hzero RCW 2
  R-H₂-zero = RP²-H₂

  source-H₁-O-from-inner : SourceO.H1Coordinates
    → PT.∥ GroupEquiv (H̃ᶜʷ (ACW octa) 1) (DirProd (ℤGroup/ 2) (ℤGroup/ 2)) ∥₁
  source-H₁-O-from-inner d = PT.map
    (λ e → compGroupEquiv (change-CW-H₁ (ACW octa) SourceO.totalCW (idEquiv _))
      (compGroupEquiv e Q₄-cokernel)) (SourceO.H₁-from-inner-MV d)

  source-H₁-I-from-inner : SourceI.H1Coordinates
    → PT.∥ GroupEquiv (H̃ᶜʷ (ACW icosa) 1) (ℤGroup/ 4) ∥₁
  source-H₁-I-from-inner d = PT.map
    (λ e → compGroupEquiv (change-CW-H₁ (ACW icosa) SourceI.totalCW (idEquiv _))
      (compGroupEquiv e Q₃-cokernel)) (SourceI.H₁-from-inner-MV d)

  target-H₁-O-from-inner : TargetO.H1Coordinates
    → PT.∥ GroupEquiv (H̃ᶜʷ (CCW octa) 1) (ℤGroup/ 2) ∥₁
  target-H₁-O-from-inner d = PT.map
    (λ e → compGroupEquiv (change-CW-H₁ (CCW octa) TargetO.totalCW (idEquiv _))
      (compGroupEquiv e G₄-cokernel)) (TargetO.H₁-from-inner-MV d)

  target-H₁-I-from-inner : TargetI.H1Coordinates
    → PT.∥ GroupEquiv (H̃ᶜʷ (CCW icosa) 1) (ℤGroup/ 1) ∥₁
  target-H₁-I-from-inner d = PT.map
    (λ e → compGroupEquiv (change-CW-H₁ (CCW icosa) TargetI.totalCW (idEquiv _))
      (compGroupEquiv e G₅-cokernel)) (TargetI.H₁-from-inner-MV d)

-- Keep construction of the four equivalences on abstract groups, too.
record FourInputs (A B C D : Type₀) : Type₀ where
  field
    source-O : A
    source-I : B
    target-O : C
    target-I : D

ComponentH1Inputs : Type₀
ComponentH1Inputs = FourInputs SourceO.H1Coordinates SourceI.H1Coordinates TargetO.H1Coordinates TargetI.H1Coordinates
module ComponentH1Inputs = FourInputs

record FourGroups (A B C D : Group₀) : Type₀ where
  field
    source-O : GroupEquiv A (DirProd (ℤGroup/ 2) (ℤGroup/ 2))
    source-I : GroupEquiv B (ℤGroup/ 4)
    target-O : GroupEquiv C (ℤGroup/ 2)
    target-I : GroupEquiv D (ℤGroup/ 1)

ComponentH1Groups : Type₀
ComponentH1Groups = FourGroups (H̃ᶜʷ (ACW octa) 1) (H̃ᶜʷ (ACW icosa) 1)
  (H̃ᶜʷ (CCW octa) 1) (H̃ᶜʷ (CCW icosa) 1)
module ComponentH1Groups = FourGroups

abstract
  assemble-groups : {A B C D : Group₀}
    → PT.∥ GroupEquiv A (DirProd (ℤGroup/ 2) (ℤGroup/ 2)) ∥₁
    → PT.∥ GroupEquiv B (ℤGroup/ 4) ∥₁
    → PT.∥ GroupEquiv C (ℤGroup/ 2) ∥₁
    → PT.∥ GroupEquiv D (ℤGroup/ 1) ∥₁
    → PT.∥ FourGroups A B C D ∥₁
  assemble-groups a b c d = PT.map2
    (λ s t → record { source-O = fst s ; source-I = snd s ; target-O = fst t ; target-I = snd t })
    (PT.map2 _,_ a b) (PT.map2 _,_ c d)

  -- Construct the component groups from the four inner cellular adapters.
  components-from-inner-MV : ComponentH1Inputs → PT.∥ ComponentH1Groups ∥₁
  components-from-inner-MV d = assemble-groups
    (source-H₁-O-from-inner (ComponentH1Inputs.source-O d))
    (source-H₁-I-from-inner (ComponentH1Inputs.source-I d))
    (target-H₁-O-from-inner (ComponentH1Inputs.target-O d))
    (target-H₁-I-from-inner (ComponentH1Inputs.target-I d))
