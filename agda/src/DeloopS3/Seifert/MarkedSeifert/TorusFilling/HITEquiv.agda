{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The torus-filling HIT equivalence retains every relator cube.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.HITEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
import Cubical.HITs.KleinBottle.Base as KB
import DeloopS3.Seifert.MarkedSeifert.WInterface as W
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Relation as R
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus

squareHIT : R.KleinRel → KB.KleinBottle
squareHIT R.vertex = KB.point
squareHIT (R.j i) = KB.line2 i
squareHIT (R.r i) = KB.line1 i
squareHIT (R.κ i k) = Square→compPath KB.square (~ i) k

pathHIT : KB.KleinBottle → R.KleinRel
pathHIT KB.point = R.vertex
pathHIT (KB.line1 i) = R.r i
pathHIT (KB.line2 i) = R.j i
pathHIT (KB.square i k) = compPath→Square (sym R.κ) i k

relToKinv : W.RelJR → Kinv
relToKinv = klein≃Kinv .fst ∘ squareHIT ∘ R.normalizeHIT

abstract
  square-section : (z : KB.KleinBottle) → squareHIT (pathHIT z) ≡ z
  square-section KB.point = refl
  square-section (KB.line1 i) = refl
  square-section (KB.line2 i) = refl
  square-section (KB.square i k) l = hcomp-equivFiller
    (λ t → compPath→Square-faces (sym KB.line1) KB.line1 KB.line2 KB.line2 i k (~ t))
    (inS (KB.square i k)) (~ l)

  path-retraction : (z : R.KleinRel) → pathHIT (squareHIT z) ≡ z
  path-retraction R.vertex = refl
  path-retraction (R.j i) = refl
  path-retraction (R.r i) = refl
  path-retraction (R.κ i k) l = cube i k l
    where
    cube : Cube ((λ i k → R.j i) ∙v' (λ i k → R.r i))
      ((λ i k → R.r (~ i)) ∙v' (λ i k → R.j i))
      (λ i k → R.vertex) (λ i k → R.vertex)
      (λ i k → pathHIT (squareHIT (R.κ i k))) R.κ
    cube = sym (∙v≡∙v' (λ i k → R.j i) (λ i k → R.r i)) ◁
      (λ i k l → hcomp-equivFiller
        (compPath→Square-faces (sym R.r) R.r R.j R.j k (~ i))
        (inS (R.κ i k)) (~ l))
      ▷ ∙v≡∙v' (λ i k → R.r (~ i)) (λ i k → R.j i)

  KleinRel≃Klein : R.KleinRel ≃ KB.KleinBottle
  KleinRel≃Klein = isoToEquiv (iso squareHIT pathHIT square-section path-retraction)

  RelJR≃Kinv : W.RelJR ≃ Kinv
  RelJR≃Kinv = relToKinv , subst isEquiv
    (cong (λ h → klein≃Kinv .fst ∘ squareHIT ∘ h) R.RelJR≃KleinRel-map)
    (compEquiv R.RelJR≃KleinRel (compEquiv KleinRel≃Klein klein≃Kinv) .snd)

  RelJR-map : RelJR≃Kinv .fst ≡ relToKinv
  RelJR-map = refl

  RelJR-base : relToKinv W.vertex ≡ kbase
  RelJR-base = refl

  RelJR-j : cong relToKinv W.j ≡ j
  RelJR-j = refl

  RelJR-r : cong relToKinv W.r ≡ r
  RelJR-r = refl
