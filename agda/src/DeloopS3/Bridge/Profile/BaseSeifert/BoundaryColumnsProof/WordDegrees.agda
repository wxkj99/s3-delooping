{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.WordDegrees where

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

-- All-input coefficient calculations, stronger than evaluation at the
-- positive generator. The negative column uses the inverse word (ab)⁻¹.
abstract
  first-word-coefficients : (r : Fin 1 → ℤ)
    → fst (bouquetDegree (Words.word-bouquet Literal.d₁)) r
      ≡ (λ { (0 , p) → r fzero ; (1 , p) → pos 0 })
  first-word-coefficients r = funExt λ
    { (0 , p) → cong (r fzero Z.·_) Words.d₁-degree-a ∙ Z.·IdR (r fzero)
    ; (1 , p) → cong (r fzero Z.·_) Words.d₁-degree-b ∙ Z.·AnnihilR (r fzero) }

  second-word-coefficients : (r : Fin 1 → ℤ)
    → fst (bouquetDegree (Words.word-bouquet Literal.d₂)) r
      ≡ (λ { (0 , p) → pos 0 ; (1 , p) → r fzero })
  second-word-coefficients r = funExt λ
    { (0 , p) → cong (r fzero Z.·_) Words.d₂-degree-a ∙ Z.·AnnihilR (r fzero)
    ; (1 , p) → cong (r fzero Z.·_) Words.d₂-degree-b ∙ Z.·IdR (r fzero) }

  third-word-coefficients : (r : Fin 1 → ℤ)
    → fst (bouquetDegree (Words.word-bouquet Literal.d₃)) r
      ≡ (λ _ → Z.- r fzero)
  third-word-coefficients r = funExt λ
    { (0 , p) → cong (r fzero Z.·_) Words.d₃-degree-a ∙ Z.·Comm (r fzero) (negsuc 0)
    ; (1 , p) → cong (r fzero Z.·_) Words.d₃-degree-b ∙ Z.·Comm (r fzero) (negsuc 0) }

