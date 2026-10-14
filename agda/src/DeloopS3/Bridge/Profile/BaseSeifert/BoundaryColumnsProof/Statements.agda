{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Statements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; secEq ; retEq)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using
  (bouquetDegree ; bouquetDegreeSusp)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using
  (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.Finite using
  (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton ; graph×circle-skeleton)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; module TorusProduct ; module GraphProduct
  ; torus-square-coordinate ; graph-square-pair)
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
open import DeloopS3.Bridge.CellularPushout.Cellular using (cellular-coefficients)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductMaps using
  (module ProductMap)
open import DeloopS3.Bridge.DegreeSpan.ProductQuotient using
  (ProductQuotientSquare ; product-quotient-from-square)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

-- Generic packaging prevents record elaboration from normalizing the
-- cellular approximation hidden in the actual H̃ᶜʷ→ implementation.
record ColumnEquations {A B : Type}
  (t : A → ℤ) (g : B → ℤ × ℤ) (f₁ f₂ f₃ : A → B) : Type where
  field
    boundary₁-column : (z : A) → g (f₁ z) ≡ (t z , pos 0)
    boundary₂-column : (z : A) → g (f₂ z) ≡ (pos 0 , t z)
    boundary₃-column : (z : A) → g (f₃ z) ≡ (Z.- t z , Z.- t z)

BoundaryColumnsStatement : Type
BoundaryColumnsStatement = ColumnEquations torus-square-coordinate graph-square-pair
  (fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₁))
  (fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₂))
  (fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₃))

-- The raw-functor statement is obtained from the sealed result
-- by transport along cellular-map-agrees.
RawBoundaryColumnsStatement : Type
RawBoundaryColumnsStatement = ColumnEquations torus-square-coordinate graph-square-pair
  (fst (H̃ᶜʷ→ {C = torusCW} {D = graph×circleCW} 2 Literal.boundary₁))
  (fst (H̃ᶜʷ→ {C = torusCW} {D = graph×circleCW} 2 Literal.boundary₂))
  (fst (H̃ᶜʷ→ {C = torusCW} {D = graph×circleCW} 2 Literal.boundary₃))

-- This is precisely the generic marked naturality lemma, with no chart
-- change or coefficient/word comparison folded into its hypothesis.
MarkedSquareNaturalityStatement : Type₁
MarkedSquareNaturalityStatement =
  (n m : ℕ) (X Y : CW₀)
  (eX : fst X ≃ realise (RoseProduct.skeleton n))
  (eY : fst Y ≃ realise (RoseProduct.skeleton m))
  (f : fst X → fst Y)
  (h : cellMap (RoseProduct.skeleton n) (RoseProduct.skeleton m))
  (agreement : realiseCellMap h ∘ fst eX ≡ fst eY ∘ f)
  (x : fst (H̃ᶜʷ X 2)) →
  MarkedProduct.square-coordinate m Y eY
    (fst (H̃ᶜʷ→ {C = X} {D = Y} 2 f) x)
  ≡ fst (cellular-coefficients h 2)
      (MarkedProduct.square-coordinate n X eX x)

