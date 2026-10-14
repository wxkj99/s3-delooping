{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCoordinateTargetChart where

-- Actual left H₂ coordinates. The source index is the petal POSITION,
-- reindexed explicitly through SumFin≃Fin; it is never a generator name.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; ¬Fin0 ; toℕ-injective)
import Cubical.Data.SumFin as SF
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠℤAbGroup)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; torus-square-coordinate)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-retraction)
open import DeloopS3.Bridge.CoverChains.Incidence using (Bdy ; RoseEdges ; Dhat)
open import DeloopS3.Cert.Input.Graph.Maps using (Petal)
import DeloopS3.Bridge.CoverChains.Words as Words
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
open Input using (ShortCase)
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
import DeloopS3.Bridge.DegreeSpan.RoseProductProjection as Projection
import DeloopS3.Bridge.DegreeSpan.InitialWordDegrees as Initial
import DeloopS3.Bridge.DegreeSpan.OverlapCoordinates as Overlap
import DeloopS3.Bridge.DegreeSpan.LeftCoordinateAlgebra as Algebra
import DeloopS3.Cert.Check as Ch
open Ch using (Kind)
open import DeloopS3.Bridge.CoverChains.Generators using (targetTorus)
import DeloopS3.Bridge.DegreeSpan.LeftCircleAction as CircleAction
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFromTorus as Circle

open import DeloopS3.Bridge.DegreeSpan.LeftCoordinateSource using (rank-two)

-- The consumer allows an explicit target marking. Use the literal
-- two-generator rose chart on the ACTUAL base-left CW space. We do not
-- assert that it equals Pieces' different Concrete realization marking.
module TargetLeft (c : ShortCase) = MarkedProduct 2 (Pieces.LᵦCW c)
  (Projection.marking 2 (Pieces.LᵦCW c)
    (Pieces.rose-product-chart Input.twoGenerators))

eLt : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (Pieces.LᵦCW c) 2) (AbGroup→Group Base.ℤ²)
eLt c = compGroupEquiv (TargetLeft.H₂ c) rank-two

-- Literal base boundary maps and their actual A/B/C columns.
target-component : (c : ShortCase) → Kind → R.T² → fst (Pieces.LᵦCW c)
target-component c k = R.Span.left (Input.BaseSpan c) ∘ Overlap.base-inclusion c k

target-exponent : Kind → SF.Fin 2 → ℤ
target-exponent k j = Words.wordExponent (P.nth 0 Input.twoGenerators (SF.toℕ j))
  (Ch.kindWord k)

abstract
  target-projected-agreement : (c : ShortCase) (k : Kind) (j : SF.Fin 2)
    → Projection.project_e 2 (Pieces.LᵦCW c)
        (Pieces.rose-product-chart Input.twoGenerators)
        (equivFun (SumFin≃Fin 2) j) ∘ target-component c k
      ≡ Circle.φ (Initial.projectedWordCircle Input.twoGenerators j (Ch.kindWord k))
  target-projected-agreement c k j = funExt λ (u , t) → ΣPathP
    ( cong (λ u → circleToC (Initial.petalProjection Input.twoGenerators j
        (R.wordCircle Input.twoGenerators (Ch.kindWord k) u)))
        (sym (circle-retraction u))
    , circle-retraction t )

