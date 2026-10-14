{-# OPTIONS --cubical --safe --lossy-unification #-}

module DeloopS3.Bridge.DegreeSpan.MarkedNaturality.Proof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_; invEq; secEq)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (cellMap; realiseCellMap)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ; H̃ᶜʷ→; H̃ˢᵏᵉˡ→)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using
  (chosen-skeleton; chosen-skeleton-path)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Groups using
  (module ProductGroups; module MarkedProduct)
open import DeloopS3.Bridge.CellularPushout.Cellular using (cellular-coefficients)
open import DeloopS3.Bridge.DegreeSpan.ProductSquareNaturality using
  (product-square-natural)
open import DeloopS3.Bridge.DegreeSpan.WitnessTransport using
  (witness-comparison; witness-comparison-natural)

abstract
  square-coordinate-factor :
    (n : ℕ) (X : CW₀)
    (e : fst X ≃ realise (RoseProduct.skeleton n))
    (x : fst (H̃ᶜʷ X 2)) →
    MarkedProduct.square-coordinate n X e x ≡
    Iso.fun (fst (ProductGroups.square-iso n))
      (fst (fst (chosen-skeleton X (RoseProduct.skeleton n , e) 2)) x)
  square-coordinate-factor n X e x = MarkedProduct.square-coordinate-factor n X e x

  -- Pass through the owners' computation lemmas before changing CW witness.
  square-coordinate-witness :
    (n : ℕ) (X : CW₀)
    (e : fst X ≃ realise (RoseProduct.skeleton n))
    (x : fst (H̃ᶜʷ X 2)) →
    MarkedProduct.square-coordinate n X e x ≡
    Iso.fun (fst (ProductGroups.square-iso n))
      (fst (fst (witness-comparison X (RoseProduct.skeleton n , e) 2)) x)
  square-coordinate-witness n X e x =
    MarkedProduct.square-coordinate-factor n X e x
    ∙ cong (Iso.fun (fst (ProductGroups.square-iso n)))
        (cong (λ c → fst (fst c) x)
          (chosen-skeleton-path X (RoseProduct.skeleton n , e) 2))

  marked-square-coordinate-natural :
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
  marked-square-coordinate-natural n m X Y eX eY f h agreement x =
    square-coordinate-witness m Y eY (fst (H̃ᶜʷ→ {C = X} {D = Y} 2 f) x)
    ∙ cong (Iso.fun (fst (ProductGroups.square-iso m)))
        (witness-comparison-natural X Y
          (RoseProduct.skeleton n , eX) (RoseProduct.skeleton m , eY) 2 f x)
    ∙ cong (Iso.fun (fst (ProductGroups.square-iso m)))
        (funExt⁻ (cong fst homology-agreement) source)
    ∙ product-square-natural n m h source
    ∙ cong (fst (cellular-coefficients h 2))
        (sym (square-coordinate-witness n X eX x))
    where
    source : fst (H̃ˢᵏᵉˡ (RoseProduct.skeleton n) 2)
    source = fst (fst (witness-comparison X (RoseProduct.skeleton n , eX) 2)) x

    u : realise (RoseProduct.skeleton n) → realise (RoseProduct.skeleton m)
    u = fst eY ∘ f ∘ invEq eX

    realised-agreement : u ≡ realiseCellMap h
    realised-agreement = funExt λ z →
      sym (funExt⁻ agreement (invEq eX z))
      ∙ cong (realiseCellMap h) (secEq eX z)

    homology-agreement :
      H̃ˢᵏᵉˡ→ {C = RoseProduct.skeleton n} {D = RoseProduct.skeleton m} 2 u
      ≡ H̃ˢᵏᵉˡ→ {C = RoseProduct.skeleton n} {D = RoseProduct.skeleton m}
          2 (realiseCellMap h)
    homology-agreement =
      cong (H̃ˢᵏᵉˡ→ {C = RoseProduct.skeleton n} {D = RoseProduct.skeleton m} 2)
        realised-agreement

