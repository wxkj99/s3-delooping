{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Products where

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

module WordProduct (d : C → Literal.P) (d₀ : d 0C ≡ Literal.p₀) where
  word : SphereBouquet 1 (Fin 1) → SphereBouquet 1 (Fin 2)
  word = Words.word-bouquet d

  h : Susp (RoseProduct.Vertices 1) → Susp (RoseProduct.Vertices 2)
  h = invEq (RoseProduct.suspension-chart 2) ∘ word
    ∘ fst (RoseProduct.suspension-chart 1)

  abstract
    h-point : h north ≡ north
    h-point = cong (invEq (RoseProduct.suspension-chart 2))
      (cong Words.word-chart d₀ ∙ Words.word-chart-point)
      ∙ retEq (RoseProduct.suspension-chart 2) north

  module PM = ProductMap 1 2 h h-point

  actual : T² → Literal.Core
  actual (u , t) = d u , t

  -- Both endpoints are the ORIGINAL marked witnesses, not the concrete
  -- witnesses used by Concrete.Inner.WordCircle.realise-agreement.
  RealizationAgreement : Type
  RealizationAgreement =
    realiseCellMap PM.cellular ∘ fst (snd torus-skeleton)
    ≡ fst (snd graph×circle-skeleton) ∘ actual

  QuotientSquare : Type
  QuotientSquare = ProductQuotientSquare 1 2 h h-point

  abstract
    conjugated-word :
      fst (RoseProduct.suspension-chart 2) ∘ h
        ∘ invEq (RoseProduct.suspension-chart 1) ≡ word
    conjugated-word = funExt λ x →
      secEq (RoseProduct.suspension-chart 2)
        (word (fst (RoseProduct.suspension-chart 1)
          (invEq (RoseProduct.suspension-chart 1) x)))
      ∙ cong word (secEq (RoseProduct.suspension-chart 1) x)

    coefficient-word : QuotientSquare
      → cellular-coefficients PM.cellular 2 ≡ bouquetDegree word
    coefficient-word q =
      cong bouquetDegree (product-quotient-from-square 1 2 h h-point q)
      ∙ sym (bouquetDegreeSusp
          (fst (RoseProduct.suspension-chart 2) ∘ h
            ∘ invEq (RoseProduct.suspension-chart 1)))
      ∙ cong bouquetDegree conjugated-word

module First = WordProduct Literal.d₁ refl
module Second = WordProduct Literal.d₂ (sym Literal.edge)
module Third = WordProduct Literal.d₃ refl

-- Separate geometric prerequisites; neither type mentions H₂ or columns.
BoundaryRealizationAgreements : Type
BoundaryRealizationAgreements = First.RealizationAgreement
  × (Second.RealizationAgreement × Third.RealizationAgreement)

BoundaryQuotientSquares : Type
BoundaryQuotientSquares = First.QuotientSquare
  × (Second.QuotientSquare × Third.QuotientSquare)

