{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ProductSquareNaturality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.ChainComplex using (CW-AugChainComplex ; H̃ˢᵏᵉˡ)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→)
open import Cubical.Algebra.ChainComplex.Homology
  using (chainComplexMap→HomologyMap)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
  using (module RoseProduct)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Cellular
  using (module ProductDifferentials)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Groups
  using (module ProductGroups)
open import DeloopS3.Bridge.CellularPushout.Cellular
  using (cellular-coefficients)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
  using (cellular-chain ; cellular-homology-β)
open import DeloopS3.Bridge.DegreeSpan.ZeroNaturality
  using (zero-differentials-natural)

abstract
  product-square-natural : (n m : ℕ)
    (h : cellMap (RoseProduct.skeleton n) (RoseProduct.skeleton m))
    (x : fst (H̃ˢᵏᵉˡ (RoseProduct.skeleton n) 2)) →
    Iso.fun (fst (ProductGroups.square-iso m))
      (fst (H̃ˢᵏᵉˡ→ {C = RoseProduct.skeleton n} {D = RoseProduct.skeleton m}
        2 (realiseCellMap h)) x)
    ≡ fst (cellular-coefficients h 2)
      (Iso.fun (fst (ProductGroups.square-iso n)) x)
  product-square-natural n m h x =
    cong (Iso.fun (fst (ProductGroups.square-iso m)))
      (funExt⁻ (cong fst (cellular-homology-β h 2)) x)
    ∙ ProductGroups.square-iso-compute m
        (fst (chainComplexMap→HomologyMap (cellular-chain h) 2) x)
    ∙ zero-differentials-natural
        (CW-AugChainComplex (RoseProduct.skeleton n))
        (CW-AugChainComplex (RoseProduct.skeleton m)) 2
        (ProductDifferentials.square-differential-zero n)
        (ProductDifferentials.above-differential-zero n)
        (ProductDifferentials.square-differential-zero m)
        (ProductDifferentials.above-differential-zero m)
        (cellular-chain h) x
    ∙ cong (fst (cellular-coefficients h 2))
        (sym (ProductGroups.square-iso-compute n x))
