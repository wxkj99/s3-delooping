{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; isContrFin1)
open import Cubical.Data.Sigma using (_×_)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_] ; ℤFinGenerator)
open import Cubical.CW.Base using (hasCWskel ; realise)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; CW-AugChainComplex)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
open import DeloopS3.Bridge.ComponentHomology.ChainTools
open import DeloopS3.Bridge.ComponentHomology.ZeroDifferentials
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW ; torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Cellular

module ProductGroups (n : ℕ) where
  open RoseProduct n
  open ProductDifferentials n

  abstract
    edge-iso : GroupIso (H̃ˢᵏᵉˡ skeleton 1) (AbGroup→Group ℤ[Fin (suc n) ])
    edge-iso = zero-differentials-iso (CW-AugChainComplex skeleton) 1
      edge-differential-zero square-differential-zero

    square-iso : GroupIso (H̃ˢᵏᵉˡ skeleton 2) (AbGroup→Group ℤ[Fin n ])
    square-iso = zero-differentials-iso (CW-AugChainComplex skeleton) 2
      square-differential-zero above-differential-zero

    -- Literal cycles in the actual augmented cellular complex.
    edge-cell : Fin (suc n) → fst (H̃ˢᵏᵉˡ skeleton 1)
    edge-cell k = SQ.[ ℤFinGenerator k ,
      funExt⁻ (cong fst edge-differential-zero) (ℤFinGenerator k) ]

    square-cell : Fin n → fst (H̃ˢᵏᵉˡ skeleton 2)
    square-cell k = SQ.[ ℤFinGenerator k ,
      funExt⁻ (cong fst square-differential-zero) (ℤFinGenerator k) ]

    edge-cell-coordinate : (k : Fin (suc n))
      → Iso.fun (fst edge-iso) (edge-cell k) ≡ ℤFinGenerator k
    edge-cell-coordinate k = refl

    square-cell-coordinate : (k : Fin n)
      → Iso.fun (fst square-iso) (square-cell k) ≡ ℤFinGenerator k
    square-cell-coordinate k = refl

    H₃-zero : isContr (fst (H̃ˢᵏᵉˡ skeleton 3))
    H₃-zero = no-cells-homology skeleton 3 refl

    square-iso-compute : (x : fst (H̃ˢᵏᵉˡ skeleton 2))
      → Iso.fun (fst square-iso) x
       ≡ Iso.fun (fst (zero-differentials-iso (CW-AugChainComplex skeleton) 2
           square-differential-zero above-differential-zero)) x
    square-iso-compute x = refl

  -- The computation retains the chosen cycle.
  abstract
    edge-cell-compute : (k : Fin (suc n))
      → edge-cell k ≡ SQ.[ ℤFinGenerator k ,
          funExt⁻ (cong fst edge-differential-zero) (ℤFinGenerator k) ]
    edge-cell-compute k = refl

-- Transport only the choice of CW witness, retaining the actual product
-- skeleton and its literal cycle representatives above.
module MarkedProduct (n : ℕ) (X : CW₀)
  (realization : fst X ≃ realise (RoseProduct.skeleton n)) where
  private
    chosen : hasCWskel (fst X)
    chosen = RoseProduct.skeleton n , realization
  open ProductGroups n

  abstract
    H₁ : GroupEquiv (H̃ᶜʷ X 1) (AbGroup→Group ℤ[Fin (suc n) ])
    H₁ = compGroupEquiv (chosen-skeleton X chosen 1) (GroupIso→GroupEquiv edge-iso)

    H₂ : GroupEquiv (H̃ᶜʷ X 2) (AbGroup→Group ℤ[Fin n ])
    H₂ = compGroupEquiv (chosen-skeleton X chosen 2) (GroupIso→GroupEquiv square-iso)

    H₃ : Hzero X 3
    H₃ = chosen-zero X chosen 3 H₃-zero

  edge-coordinate : fst (H̃ᶜʷ X 1) → (Fin (suc n) → ℤ)
  edge-coordinate = fst (fst H₁)

  square-coordinate : fst (H̃ᶜʷ X 2) → (Fin n → ℤ)
  square-coordinate = fst (fst H₂)

  abstract
    edge-generator : Fin (suc n) → fst (H̃ᶜʷ X 1)
    edge-generator k = invEq (fst (chosen-skeleton X chosen 1)) (edge-cell k)

    square-generator : Fin n → fst (H̃ᶜʷ X 2)
    square-generator k = invEq (fst (chosen-skeleton X chosen 2)) (square-cell k)

    edge-generator-coordinate : (k : Fin (suc n))
      → edge-coordinate (edge-generator k) ≡ ℤFinGenerator k
    edge-generator-coordinate k = cong (Iso.fun (fst edge-iso))
      (secEq (fst (chosen-skeleton X chosen 1)) (edge-cell k))
      ∙ edge-cell-coordinate k

    square-generator-coordinate : (k : Fin n)
      → square-coordinate (square-generator k) ≡ ℤFinGenerator k
    square-generator-coordinate k = cong (Iso.fun (fst square-iso))
      (secEq (fst (chosen-skeleton X chosen 2)) (square-cell k))
      ∙ square-cell-coordinate k

    square-coordinate-factor : (x : fst (H̃ᶜʷ X 2))
      → square-coordinate x
       ≡ Iso.fun (fst square-iso)
           (fst (fst (chosen-skeleton X (RoseProduct.skeleton n , realization) 2)) x)
    square-coordinate-factor x = refl

  -- Computation interface for literal degree-one markings.
  abstract
    edge-coordinate-factor : (x : fst (H̃ᶜʷ X 1))
      → edge-coordinate x
       ≡ Iso.fun (fst edge-iso)
           (fst (fst (chosen-skeleton X (RoseProduct.skeleton n , realization) 1)) x)
    edge-coordinate-factor x = refl

