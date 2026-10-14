{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.RoseProductProjection where

-- Actual H₂ petal projections for an arbitrarily marked finite rose × S¹.
-- The marking is the given equivalence followed by the original product
-- skeleton chart.  The map, cellular realization, and quotient degrees are
-- all constructed; there is no realization-agreement premise.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_ ; compEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin ; fzero ; isContrFin1)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Pushout using (inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤ[Fin_] ; ℤFinGenerator ; agreeOnℤFinGenerator→≡ ; isGeneratorℤFinGenerator')
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (realiseCellMap)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; torus-square-coordinate)
open import DeloopS3.Bridge.CellularPushout.Cellular using (cellular-coefficients)
open import DeloopS3.Move.CancelMinimal using (T²)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC)
import DeloopS3.Bridge.DegreeSpan.MarkedNaturality.Proof as Marked
import DeloopS3.Bridge.DegreeSpan.RoseProductProjectionSparse as Sparse
import DeloopS3.Bridge.DegreeSpan.RoseProductProjectionRealization as Realization

project_e : (n : ℕ) (Y : CW₀) (e : fst Y ≃ (RoseProduct.Rose n × S¹))
  → Fin n → fst Y → T²
project_e n Y e j y =
  circleToC (pickPetal j (fst (fst e y))) , circleToC (snd (fst e y))

marking : (n : ℕ) (Y : CW₀) (e : fst Y ≃ (RoseProduct.Rose n × S¹))
  → fst Y ≃ realise (RoseProduct.skeleton n)
marking n Y e = compEquiv e (snd (RoseProduct.has-skeleton n))

coordinate-projection : (n : ℕ) (j : Fin n)
  → GroupHom (AbGroup→Group ℤ[Fin n ]) (AbGroup→Group ℤ[Fin 1 ])
fst (coordinate-projection n j) r _ = r j
snd (coordinate-projection n j) = makeIsGroupHom (λ _ _ → refl)

abstract
  projection-coefficients-from-degrees : (n : ℕ) (j : Fin n)
    (F : SphereBouquet 2 (Fin n) → SphereBouquet 2 (Fin 1))
    → ((k : Fin n)
      → degree 2 (λ s → pickPetal fzero (F (inr (k , s)))) ≡ ℤFinGenerator k j)
    → bouquetDegree F ≡ coordinate-projection n j
  projection-coefficients-from-degrees n j F degrees =
    agreeOnℤFinGenerator→≡
      {ϕ = bouquetDegree F} {ψ = coordinate-projection n j}
      λ k → funExt λ b →
        sym (isGeneratorℤFinGenerator'
          (λ t → degree 2 (λ s → pickPetal b (F (inr (t , s))))) k)
        ∙ cong (λ b' → degree 2 (λ s → pickPetal b' (F (inr (k , s)))))
            (sym (snd isContrFin1 b))
        ∙ degrees k

  sparseCellular-coefficients : (n : ℕ) (j : Fin n)
    → cellular-coefficients (Sparse.sparseCellular n j) 2 ≡ coordinate-projection n j
  sparseCellular-coefficients n j =
    projection-coefficients-from-degrees n j
      (Sparse.cellular-square-quotient n (Sparse.sparseCellular n j))
      (Sparse.sparseCellular-degree n j)

  marked-agreement : (n : ℕ) (Y : CW₀)
    (e : fst Y ≃ (RoseProduct.Rose n × S¹)) (j : Fin n)
    → realiseCellMap (Sparse.sparseCellular n j) ∘ fst (marking n Y e)
      ≡ fst (snd torus-skeleton) ∘ project_e n Y e j
  marked-agreement n Y e j = funExt λ y →
    funExt⁻ (Realization.sparse-marked-agreement n j) (fst e y)

  -- Both sides of the projection formula use the supplied marking e.
  project-H₂ : (n : ℕ) (Y : CW₀)
    (e : fst Y ≃ (RoseProduct.Rose n × S¹)) (j : Fin n)
    (z : fst (H̃ᶜʷ Y 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = Y} {D = torusCW} 2 (project_e n Y e j)) z)
      ≡ MarkedProduct.square-coordinate n Y (marking n Y e) z j
  project-H₂ n Y e j z =
    cong (λ r → r fzero)
      (Marked.marked-square-coordinate-natural n 1 Y torusCW
        (marking n Y e) (snd torus-skeleton) (project_e n Y e j)
        (Sparse.sparseCellular n j) (marked-agreement n Y e j) z)
    ∙ cong (λ (d : GroupHom (AbGroup→Group ℤ[Fin n ]) (AbGroup→Group ℤ[Fin 1 ]))
        → fst d (MarkedProduct.square-coordinate n Y (marking n Y e) z) fzero)
        (sparseCellular-coefficients n j)
