{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof where

-- Derive the three H₂ columns from realization agreements and product quotient squares.
-- Marked homology naturality is supplied without identifying opaque realization charts.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sigma using (_×_)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using
  (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.Finite using
  (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module TorusProduct ; torus-square-coordinate ; graph-square-pair)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns as Base
import DeloopS3.Bridge.DegreeSpan.MarkedNaturality.Proof as Marked

-- At this public entry point, BoundaryColumnsStatement is the exact RAW
-- H̃ᶜʷ→ statement. The sealed variant is exported separately for integration.
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Statements public
  renaming (BoundaryColumnsStatement to SealedBoundaryColumnsStatement
          ; RawBoundaryColumnsStatement to BoundaryColumnsStatement)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Products public
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.WordDegrees public
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Naturality public

private
  pair : (Fin 2 → ℤ) → ℤ × ℤ
  pair f = f fzero , f (fsuc fzero)

  -- Do path transport generically, before substituting the large actual
  -- homology maps. All endpoint functions have explicit carrier types.
  abstract
    transport-columns : {A B : Type} (t : A → ℤ) (g : B → ℤ × ℤ)
      {f₁ f₂ f₃ k₁ k₂ k₃ : A → B}
      → f₁ ≡ k₁ → f₂ ≡ k₂ → f₃ ≡ k₃
      → ColumnEquations t g f₁ f₂ f₃ → ColumnEquations t g k₁ k₂ k₃
    transport-columns t g p q r =
      transport (λ i → ColumnEquations t g (p i) (q i) (r i))

abstract
  -- The constructor with explicit marked naturality and geometric inputs.
  boundary-columns-sealed : MarkedSquareNaturalityStatement
    → BoundaryRealizationAgreements → BoundaryQuotientSquares
    → SealedBoundaryColumnsStatement
  ColumnEquations.boundary₁-column (boundary-columns-sealed natural agreements squares) z =
    cong pair (FirstNaturality.marked-coordinates natural (fst agreements) (fst squares) z
      ∙ first-word-coefficients (TorusProduct.square-coordinate z))
  ColumnEquations.boundary₂-column (boundary-columns-sealed natural agreements squares) z =
    cong pair (SecondNaturality.marked-coordinates natural (fst (snd agreements)) (fst (snd squares)) z
      ∙ second-word-coefficients (TorusProduct.square-coordinate z))
  ColumnEquations.boundary₃-column (boundary-columns-sealed natural agreements squares) z =
    cong pair (ThirdNaturality.marked-coordinates natural (snd (snd agreements)) (snd (snd squares)) z
      ∙ third-word-coefficients (TorusProduct.square-coordinate z))

  sealed-to-raw : SealedBoundaryColumnsStatement → BoundaryColumnsStatement
  sealed-to-raw = transport-columns torus-square-coordinate graph-square-pair
    (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₁))
    (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₂))
    (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₃))

  boundary-columns-with-naturality : MarkedSquareNaturalityStatement
    → BoundaryRealizationAgreements → BoundaryQuotientSquares
    → BoundaryColumnsStatement
  boundary-columns-with-naturality natural agreements squares =
    sealed-to-raw (boundary-columns-sealed natural agreements squares)

  marked-square-naturality : MarkedSquareNaturalityStatement
  marked-square-naturality = Marked.marked-square-coordinate-natural

  -- Specialize generic marked naturality, retaining the two geometric inputs.
  boundary-columns : BoundaryRealizationAgreements → BoundaryQuotientSquares
    → BoundaryColumnsStatement
  boundary-columns = boundary-columns-with-naturality marked-square-naturality

  to-base-seifert : SealedBoundaryColumnsStatement → Base.BoundaryColumns
  Base.BoundaryColumns.boundary₁-column (to-base-seifert columns) =
    ColumnEquations.boundary₁-column columns
  Base.BoundaryColumns.boundary₂-column (to-base-seifert columns) =
    ColumnEquations.boundary₂-column columns
  Base.BoundaryColumns.boundary₃-column (to-base-seifert columns) =
    ColumnEquations.boundary₃-column columns

  base-seifert-boundary-columns : BoundaryRealizationAgreements → BoundaryQuotientSquares
    → Base.BoundaryColumns
  base-seifert-boundary-columns agreements squares =
    to-base-seifert (boundary-columns-sealed marked-square-naturality agreements squares)
