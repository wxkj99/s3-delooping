{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusIntegerH2 where

-- The same LES boundary is used on BOTH sides of every endomorphism.
-- Its injectivity, not a rank computation or an orientation choice, proves
-- intrinsic scalar action. The original torus coordinate then preserves it.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isContrΣ ; isPropΠ)
open import Cubical.Data.Int using (ℤ ; isSetℤ)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp ; H̃ᶜʷ→Equiv)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Circle using (circleCW ; circle-H≥2 ; C-finite)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using (torus-H₂)
open import DeloopS3.Bridge.DMCExactness.Geometric using (GeometricPushoutLES ; SpanSequenceData)
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)
open import DeloopS3.Bridge.DegreeSpan.TorusMultiplierH2 using (TorusMultiplierH₂Scalar)
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerAlgebra
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerCylinder
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerCircle using (overlap-multiplier-scalar)
open import DeloopS3.Move.CancelMinimal using (mulC)
import DeloopS3.Bridge.DegreeSpan.Map as Map
open import DeloopS3.Bridge.DegreeSpan.LowerBoundaryDescent using
  (finite≤-same-span-boundary-natural)

CylinderLES : Type₁
CylinderLES = GeometricPushoutLES overlapCW circleCW circleCW
  CylinderC.fold CylinderC.fold cylinderCW

-- One LES witness with naturality for every continuous endospan map.
-- The package adds no H₂ group, rank, or chart assumptions.
SameBoundary : Type₁
SameBoundary = Σ[ les ∈ CylinderLES ]
  ((m : Map.ContinuousSpanMap CylinderC.span CylinderC.span)
    → compGroupHom
        (H̃ᶜʷ→ {C = cylinderCW} {D = cylinderCW} 2 (Map.totalMap m))
        (SpanSequenceData.boundary (snd les) 1)
      ≡ compGroupHom
        (SpanSequenceData.boundary (snd les) 1)
        (H̃ᶜʷ→ {C = overlapCW} {D = overlapCW} 1 (Map.overlapMap m)))

cylinder-map : ℤ → GroupHom (H̃ᶜʷ cylinderCW 2) (H̃ᶜʷ cylinderCW 2)
cylinder-map ℓ = H̃ᶜʷ→ {C = cylinderCW} {D = cylinderCW} 2
  (Map.totalMap (CylinderC.endomap (mulC ℓ)))

torus-map : ℤ → GroupHom (H̃ᶜʷ torusCW 2) (H̃ᶜʷ torusCW 2)
torus-map ℓ = H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 (TorusMultiplier.actual ℓ)

abstract
  torus-cylinder-H₂ : GroupEquiv (H̃ᶜʷ torusCW 2) (H̃ᶜʷ cylinderCW 2)
  torus-cylinder-H₂ = H̃ᶜʷ→Equiv {C = torusCW} {D = cylinderCW} 2 torus-cylinder

  torus-cylinder-H₂-natural : (ℓ : ℤ) (x : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst torus-cylinder-H₂) (fst (torus-map ℓ) x)
      ≡ fst (cylinder-map ℓ) (equivFun (fst torus-cylinder-H₂) x)
  torus-cylinder-H₂-natural ℓ x = cong (λ h → fst h x)
    (sym (H̃ᶜʷ→comp {C = torusCW} {D = torusCW} {E = cylinderCW} 2
      (equivFun torus-cylinder) (TorusMultiplier.actual ℓ))
      ∙ cong (H̃ᶜʷ→ {C = torusCW} {D = cylinderCW} 2)
          (sym (torus-cylinder-natural (mulC ℓ)))
      ∙ H̃ᶜʷ→comp {C = torusCW} {D = cylinderCW} {E = cylinderCW} 2
          (Map.totalMap (CylinderC.endomap (mulC ℓ))) (equivFun torus-cylinder))

module FromSameBoundary (package : SameBoundary) where
  private
    module L = SpanSequenceData (snd (fst package))

  abstract
    cylinder-multiplier-intrinsic : (ℓ : ℤ)
      → Scalar (H̃ᶜʷ cylinderCW 2) ℓ (cylinder-map ℓ)
    cylinder-multiplier-intrinsic ℓ = scalar-from-boundary
      {V = DirProd (H̃ᶜʷ circleCW 2) (H̃ᶜʷ circleCW 2)}
      {P = H̃ᶜʷ cylinderCW 2} {A = H̃ᶜʷ overlapCW 1}
      (L.sum-map 2) (L.boundary 1) (cylinder-map ℓ)
      (H̃ᶜʷ→ {C = overlapCW} {D = overlapCW} 1
        (Map.overlapMap (CylinderC.endomap (mulC ℓ)))) ℓ
      (L.exact-total 1 (3 , refl))
      (isContrΣ (circle-H≥2 0) (λ _ → circle-H≥2 0))
      (snd package (CylinderC.endomap (mulC ℓ)))
      (overlap-multiplier-scalar ℓ)

    torus-multiplier-intrinsic : (ℓ : ℤ)
      → Scalar (H̃ᶜʷ torusCW 2) ℓ (torus-map ℓ)
    torus-multiplier-intrinsic ℓ = scalar-through-equiv torus-cylinder-H₂
      (torus-map ℓ) (cylinder-map ℓ) ℓ (torus-cylinder-H₂-natural ℓ)
      (cylinder-multiplier-intrinsic ℓ)

    torus-multiplier-coordinate : (ℓ : ℤ) → TorusMultiplierH₂Scalar ℓ
    torus-multiplier-coordinate ℓ = scalar-coordinate (torus-map ℓ)
      (GroupEquiv→GroupHom torus-H₂) ℓ (torus-multiplier-intrinsic ℓ)

abstract
  torus-multiplier-H₂-from-same-boundary : PT.∥ SameBoundary ∥₁
    → (ℓ : ℤ) → TorusMultiplierH₂Scalar ℓ
  torus-multiplier-H₂-from-same-boundary package ℓ =
    PT.rec (isPropΠ (λ _ → isSetℤ _ _))
      (λ p → FromSameBoundary.torus-multiplier-coordinate p ℓ) package

  cylinder-same-boundary : PT.∥ SameBoundary ∥₁
  cylinder-same-boundary = finite≤-same-span-boundary-natural
    overlapCW circleCW circleCW 1 1 1 overlap-finite C-finite C-finite
    CylinderC.fold CylinderC.fold (snd cylinderCW)

  -- All integers, on the actual map, in the original square coordinate.
  torus-multiplier-H₂ : (ℓ : ℤ) → TorusMultiplierH₂Scalar ℓ
  torus-multiplier-H₂ = torus-multiplier-H₂-from-same-boundary cylinder-same-boundary
