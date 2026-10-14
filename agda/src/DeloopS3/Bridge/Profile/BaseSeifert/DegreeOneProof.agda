{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.Group using (GroupStr)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.DMCExactness.Geometric using (actual-source)
open import DeloopS3.Bridge.SeifertChains.Matrices using (Araw)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (overlapCW ; fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates using (overlap-H₁ ; vertices-H₁)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (signed-hom-eval)
import DeloopS3.Bridge.Profile.BaseSeifert.Reduction as Reduction
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Assembly as Assembly
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components as Components
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

module Actual = Assembly.Assemble
  (H̃ᶜʷ overlapCW 1) (H̃ᶜʷ graph×circleCW 1) (H̃ᶜʷ fillingsCW 1)
  overlap-H₁ vertices-H₁
  Components.source-u1 Components.source-u2 Components.source-u3
  Components.source-h1 Components.source-h2 Components.source-h3
  Components.core-a-class Components.core-b-class Components.core-h-class
  Components.filling1-integer Components.filling2-integer Components.filling3-integer

-- Parameter-independent chart identification: six source and six vertex
-- generator normalizations, with no signed-source matrix equation as input.
HurewiczChartIdentification : Type
HurewiczChartIdentification = Actual.Markings

DegreeOneStatement : (p q r : ℤ) → Type
DegreeOneStatement p q r = (z : fst (H̃ᶜʷ overlapCW 1)) →
  equivFun (fst vertices-H₁)
    (actual-source overlapCW graph×circleCW fillingsCW
      (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 1 z)
  ≡ fst (Araw p q r) (equivFun (fst overlap-H₁) z)

abstract
  statement-agrees : (p q r : ℤ)
    → DegreeOneStatement p q r ≡ Reduction.DegreeOneComparison p q r
  statement-agrees p q r = refl

  -- These twelve actual map equations need no chart-identification hypothesis.
  actual-word-images : (p q r : ℤ)
    → Actual.WordImages p q r (Components.left-map p q r) (Components.right-map p q r)
  Actual.WordImages.left-u1 (actual-word-images p q r) = Components.left-u1 p q r
  Actual.WordImages.left-u2 (actual-word-images p q r) = Components.left-u2 p q r
  Actual.WordImages.left-u3 (actual-word-images p q r) = Components.left-u3 p q r
  Actual.WordImages.left-h1 (actual-word-images p q r) = Components.left-h1 p q r
  Actual.WordImages.left-h2 (actual-word-images p q r) = Components.left-h2 p q r
  Actual.WordImages.left-h3 (actual-word-images p q r) = Components.left-h3 p q r
  Actual.WordImages.right-u1 (actual-word-images p q r) = Components.right-u1 p q r
  Actual.WordImages.right-u2 (actual-word-images p q r) = Components.right-u2 p q r
  Actual.WordImages.right-u3 (actual-word-images p q r) = Components.right-u3 p q r
  Actual.WordImages.right-h1 (actual-word-images p q r) = Components.right-h1 p q r
  Actual.WordImages.right-h2 (actual-word-images p q r) = Components.right-h2 p q r
  Actual.WordImages.right-h3 (actual-word-images p q r) = Components.right-h3 p q r

  degree-one-proof : HurewiczChartIdentification → (p q r : ℤ) → DegreeOneStatement p q r
  degree-one-proof markings p q r z =
    cong (equivFun (fst vertices-H₁))
      (sym (signed-hom-eval overlapCW graph×circleCW fillingsCW 0
        (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) z))
    ∙ Actual.degree-one markings p q r
        (Components.left-map p q r) (Components.right-map p q r)
        (Reduction.seifert-source p q r 0) s-eval (actual-word-images p q r) z
    where
    s-eval : (x : fst (H̃ᶜʷ overlapCW 1))
      → fst (Reduction.seifert-source p q r 0) x
        ≡ (fst (Components.left-map p q r) x ,
           GroupStr.inv (snd (H̃ᶜʷ fillingsCW 1)) (fst (Components.right-map p q r) x))
    s-eval = signed-hom-eval overlapCW graph×circleCW fillingsCW 0
      (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r)

  degree-one-comparison : HurewiczChartIdentification → (p q r : ℤ)
    → Reduction.DegreeOneComparison p q r
  degree-one-comparison markings p q r = degree-one-proof markings p q r

  degree-one-234 : HurewiczChartIdentification
    → Reduction.DegreeOneComparison (pos 2) (pos 3) (pos 4)
  degree-one-234 markings = degree-one-comparison markings (pos 2) (pos 3) (pos 4)

  degree-one-235 : HurewiczChartIdentification
    → Reduction.DegreeOneComparison (pos 2) (pos 3) (pos 5)
  degree-one-235 markings = degree-one-comparison markings (pos 2) (pos 3) (pos 5)

  degree-one-223 : HurewiczChartIdentification
    → Reduction.DegreeOneComparison (pos 2) (pos 2) (pos 3)
  degree-one-223 markings = degree-one-comparison markings (pos 2) (pos 2) (pos 3)

  degree-one-224 : HurewiczChartIdentification
    → Reduction.DegreeOneComparison (pos 2) (pos 2) (pos 4)
  degree-one-224 markings = degree-one-comparison markings (pos 2) (pos 2) (pos 4)
