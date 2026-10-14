{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ProjectH2 where

-- Petal projection, sparse quotient degrees, and the marked H₂ reduction.
-- ProjectH2Realization supplies the cellular map and agreement for project-H₂.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; isContrFin1)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤ[Fin_] ; ℤFinGenerator ; agreeOnℤFinGenerator→≡ ; isGeneratorℤFinGenerator')
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.HITs.Pushout using (inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton ; graph×circle-skeleton)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module GraphProduct ; torus-square-coordinate)
open import DeloopS3.Bridge.CellularPushout.Cellular using
  (restrictCell ; cellular-coefficients)
open import DeloopS3.Bridge.CellularPushout.CellGroups using (petal-degree)
import DeloopS3.Bridge.DegreeSpan.MarkedNaturality.Proof as Marked
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Move.CancelMinimal using (T²)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC)

project : Fin 2 → Literal.Core → T²
project j (u , t) = circleToC (pickPetal j (Words.word-chart u)) , t

coordinate-projection : (j : Fin 2)
  → GroupHom (AbGroup→Group ℤ[Fin 2 ]) (AbGroup→Group ℤ[Fin 1 ])
fst (coordinate-projection j) r _ = r j
snd (coordinate-projection j) = makeIsGroupHom (λ _ _ → refl)

-- The sparse quotient model selects one petal. ProjectH2Sparse identifies
-- the quotient of its cellular map with this model at the coefficient level.
sparse-quotient : Fin 2 → SphereBouquet 2 (Fin 2) → SphereBouquet 2 (Fin 1)
sparse-quotient j x = inr (fzero , pickPetal j x)

abstract
  sparse-quotient-degree : (j k : Fin 2)
    → degree 2 (λ s → pickPetal fzero (sparse-quotient j (inr (k , s))))
      ≡ ℤFinGenerator k j
  sparse-quotient-degree j k = petal-degree 2 k j

  projection-coefficients-from-degrees : (j : Fin 2)
    (F : SphereBouquet 2 (Fin 2) → SphereBouquet 2 (Fin 1))
    → ((k : Fin 2)
      → degree 2 (λ s → pickPetal fzero (F (inr (k , s)))) ≡ ℤFinGenerator k j)
    → bouquetDegree F ≡ coordinate-projection j
  projection-coefficients-from-degrees j F degrees =
    agreeOnℤFinGenerator→≡
      {ϕ = bouquetDegree F} {ψ = coordinate-projection j}
      λ k → funExt λ b →
        sym (isGeneratorℤFinGenerator'
          (λ t → degree 2 (λ s → pickPetal b (F (inr (t , s))))) k)
        ∙ cong (λ b' → degree 2 (λ s → pickPetal b' (F (inr (k , s)))))
            (sym (snd isContrFin1 b))
        ∙ degrees k

  sparse-quotient-coefficients : (j : Fin 2)
    → bouquetDegree (sparse-quotient j) ≡ coordinate-projection j
  sparse-quotient-coefficients j =
    projection-coefficients-from-degrees j (sparse-quotient j)
      (sparse-quotient-degree j)

cellular-square-quotient : cellMap (RoseProduct.skeleton 2) (RoseProduct.skeleton 1)
  → SphereBouquet 2 (Fin 2) → SphereBouquet 2 (Fin 1)
cellular-square-quotient h =
  prefunctoriality.bouquetFunct 3 (restrictCell h 3) (2 , <ᵗsuc {m = 2})

abstract
  project-H₂-from-degrees : (j : Fin 2)
    (h : cellMap (RoseProduct.skeleton 2) (RoseProduct.skeleton 1))
    (agreement : realiseCellMap h ∘ fst (snd graph×circle-skeleton)
      ≡ fst (snd torus-skeleton) ∘ project j)
    (degrees : (k : Fin 2)
      → degree 2 (λ s → pickPetal fzero (cellular-square-quotient h (inr (k , s))))
        ≡ ℤFinGenerator k j)
    (z : fst (H̃ᶜʷ graph×circleCW 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = graph×circleCW} {D = torusCW} 2 (project j)) z)
      ≡ GraphProduct.square-coordinate z j
  project-H₂-from-degrees j h agreement degrees z =
    cong (λ r → r fzero)
      (Marked.marked-square-coordinate-natural 2 1 graph×circleCW torusCW
        (snd graph×circle-skeleton) (snd torus-skeleton) (project j) h agreement z)
    ∙ cong (λ (d : GroupHom (AbGroup→Group ℤ[Fin 2 ]) (AbGroup→Group ℤ[Fin 1 ]))
        → fst d (GraphProduct.square-coordinate z) fzero)
        (projection-coefficients-from-degrees j (cellular-square-quotient h) degrees)

