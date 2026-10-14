{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Naturality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Fin using (Fin)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using
  (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.Finite using
  (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton ; graph×circle-skeleton)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; module TorusProduct ; module GraphProduct)
open import DeloopS3.Bridge.CellularPushout.Cellular using (cellular-coefficients)
open import DeloopS3.Move.CancelMinimal using (C ; 0C)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Statements
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Products

-- Seal while CW endpoints and realization maps are still variables.
abstract
  sealed-marked-natural : MarkedSquareNaturalityStatement
    → (n m : ℕ) (X Y : CW₀)
    (eX : fst X ≃ realise (RoseProduct.skeleton n))
    (eY : fst Y ≃ realise (RoseProduct.skeleton m))
    (f : fst X → fst Y)
    (h : cellMap (RoseProduct.skeleton n) (RoseProduct.skeleton m))
    (agreement : realiseCellMap h ∘ fst eX ≡ fst eY ∘ f)
    (x : fst (H̃ᶜʷ X 2)) →
    MarkedProduct.square-coordinate m Y eY
      (fst (cellular-map X Y 2 f) x)
    ≡ fst (cellular-coefficients h 2)
        (MarkedProduct.square-coordinate n X eX x)
  sealed-marked-natural natural n m X Y eX eY f h agreement x =
    cong (MarkedProduct.square-coordinate m Y eY)
      (funExt⁻ (cong fst (cellular-map-agrees X Y 2 f)) x)
    ∙ natural n m X Y eX eY f h agreement x

module WordProductNaturality (d : C → Literal.P) (d₀ : d 0C ≡ Literal.p₀) where
  open WordProduct d d₀

  abstract
    marked-coordinates : MarkedSquareNaturalityStatement
      → RealizationAgreement → QuotientSquare
      → (z : fst (H̃ᶜʷ torusCW 2))
      → GraphProduct.square-coordinate
          (fst (cellular-map torusCW graph×circleCW 2 actual) z)
        ≡ fst (bouquetDegree word) (TorusProduct.square-coordinate z)
    marked-coordinates natural agreement q z =
      sealed-marked-natural natural 1 2 torusCW graph×circleCW
        (snd torus-skeleton) (snd graph×circle-skeleton)
        actual PM.cellular agreement z
      ∙ cong (λ (k : GroupHom (AbGroup→Group ℤ[Fin 1 ]) (AbGroup→Group ℤ[Fin 2 ]))
          → fst k (TorusProduct.square-coordinate z)) (coefficient-word q)

module FirstNaturality = WordProductNaturality Literal.d₁ refl
module SecondNaturality = WordProductNaturality Literal.d₂ (sym Literal.edge)
module ThirdNaturality = WordProductNaturality Literal.d₃ refl
