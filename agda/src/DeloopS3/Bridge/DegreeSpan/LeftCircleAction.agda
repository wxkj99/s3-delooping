{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCircleAction where

-- A first-factor circle map acts on the actual torus H₂ by its integer
-- degree, in the original marked square coordinate. No product-homology
-- formula or realization hypothesis is assumed.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.S1.Base using (S¹ ; winding ; intLoop ; windingℤLoop)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; torus-square-coordinate)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-retraction)
open import DeloopS3.Move.CancelMinimal using (T² ; mulC)
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFromTorus as Circle
import DeloopS3.Bridge.DegreeSpan.TorusIntegerH2 as Integer
import DeloopS3.Bridge.DegreeSpan.RoseProductProjection as Projection

integer-circle : ℤ → S¹ → S¹
integer-circle ℓ = CToCircle ∘ mulC ℓ ∘ circleToC

torus-action : (T² → T²) → fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ torusCW 2)
torus-action f = fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 f)

abstract
  integer-circle-degree : (ℓ : ℤ) → degree 1 (integer-circle ℓ) ≡ ℓ
  integer-circle-degree ℓ = cong winding (cong intLoop (Z.·IdR ℓ))
    ∙ windingℤLoop ℓ

  integer-circle-torus : (ℓ : ℤ)
    → Circle.φ (integer-circle ℓ) ≡ TorusMultiplier.actual ℓ
  integer-circle-torus ℓ = funExt λ (u , t) i →
    (circle-retraction (mulC ℓ (circleToC (CToCircle u)))
      ∙ cong (mulC ℓ) (circle-retraction u)) i , t

  circle-action-integer : (f : S¹ → S¹) (ℓ : ℤ)
    → degree 1 f ≡ ℓ → (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate (torus-action (Circle.φ f) z)
      ≡ ℓ Z.· torus-square-coordinate z
  circle-action-integer f ℓ p z =
    Circle.circle-action-degree {f = f} {g = integer-circle ℓ}
      (p ∙ sym (integer-circle-degree ℓ)) z
    ∙ Circle.coordinate-map-path torus-action torus-square-coordinate
        (integer-circle-torus ℓ) z
    ∙ Integer.torus-multiplier-H₂ ℓ z

  -- Per-component coefficient extraction for an arbitrary marked rose.
  -- Agreement names the actual projected map, not a cellular surrogate.
  projected-component-H₂ : (n : ℕ) (Y : CW₀)
    (e : fst Y ≃ (RoseProduct.Rose n × S¹)) (j : Fin n)
    (F : T² → fst Y) (f : S¹ → S¹) (ℓ : ℤ)
    → Projection.project_e n Y e j ∘ F ≡ Circle.φ f
    → degree 1 f ≡ ℓ → (z : fst (H̃ᶜʷ torusCW 2))
    → MarkedProduct.square-coordinate n Y (Projection.marking n Y e)
        (fst (H̃ᶜʷ→ {C = torusCW} {D = Y} 2 F) z) j
      ≡ ℓ Z.· torus-square-coordinate z
  projected-component-H₂ n Y e j F f ℓ agreement d z =
    sym (Projection.project-H₂ n Y e j
      (fst (H̃ᶜʷ→ {C = torusCW} {D = Y} 2 F) z))
    ∙ cong (λ h → torus-square-coordinate (fst h z))
        (sym (H̃ᶜʷ→comp {C = torusCW} {D = Y} {E = torusCW}
          2 (Projection.project_e n Y e j) F))
    ∙ Circle.coordinate-map-path torus-action torus-square-coordinate agreement z
    ∙ circle-action-integer f ℓ d z
