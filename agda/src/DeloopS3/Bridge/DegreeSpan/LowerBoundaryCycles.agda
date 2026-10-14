{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerBoundaryCycles where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗ-trans ; <ᵗsuc)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Finite
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base using (CWskel)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.ChainComplex using (CW-AugChainComplex ; H̃ˢᵏᵉˡ)
open import DeloopS3.Bridge.CellularPushout.Cellular
  using (CW-augmented ; cellular-augmented-map)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
  using (presentation-map)
open import DeloopS3.Bridge.DMCExactness.Quotient using (module Homology)
open import DeloopS3.Bridge.DMCExactness.Maps using (module ConeMaps)
import DeloopS3.Bridge.CellularPushout.PrismChains as PC
import DeloopS3.Bridge.CellularPushout.PrismRetraction as PR

open import DeloopS3.Bridge.DegreeSpan.TopBoundaryCycles
  using (chain-cycle ; chain-cycle-β ; finite-cycle ; finite-cycle-β) public

-- Ordinary total H2 uses augmented coefficient 3; overlap H1 uses 2.
module SpecifiedBoundary (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where

  module Q = PC.PrismChains A B C f g
  module P = Q.CP.P
  module R = PR.PrismRetraction A B C f g
  module M = ConeMaps (CW-augmented P.B) (CW-augmented P.C) (CW-augmented P.D)
    (cellular-augmented-map P.f) (cellular-augmented-map P.g)
  module HY = Homology (CW-AugChainComplex P.pushoutSkel) 2
  module HX = Homology (CW-AugChainComplex P.B) 1

  χ-cycle : HY.Cycle → M.HD.Cycle 2
  χ-cycle = chain-cycle Q.χ-chain 2

  R-cycle : HY.Cycle → HX.Cycle
  R-cycle z = chain-cycle (presentation-map P.B) 1
    (fst (M.projection 1) (χ-cycle z))

  δ : GroupHom (H̃ˢᵏᵉˡ P.pushoutSkel 2) (H̃ˢᵏᵉˡ P.B 1)
  δ = compGroupHom (chainComplexMap→HomologyMap Q.χ-chain 2)
    (compGroupHom (M.δ 1) (chainComplexMap→HomologyMap (presentation-map P.B) 1))

  δ-inverse : GroupHom (H̃ˢᵏᵉˡ P.pushoutSkel 2) (H̃ˢᵏᵉˡ P.B 1)
  δ-inverse = compGroupHom
    (chainComplexMap→HomologyMap (invChainMap Q.q-chain-equivalence) 2)
    (compGroupHom (M.δ 1)
      (chainComplexMap→HomologyMap (presentation-map P.B) 1))

  abstract
    δ-inverse-comparison-agrees : δ-inverse ≡ δ
    δ-inverse-comparison-agrees = cong
      (λ h → compGroupHom (chainComplexMap→HomologyMap h 2)
        (compGroupHom (M.δ 1)
          (chainComplexMap→HomologyMap (presentation-map P.B) 1)))
      Q.inverse-chain-agrees

    R-cycle-coefficient : (z : HY.Cycle) → fst (R-cycle z) ≡ fst (R.R 1) (fst z)
    R-cycle-coefficient z = funExt⁻ (cong fst (Q.χ-relative 1)) (fst z)

    δ-cycle-β : (z : HY.Cycle) → fst δ (HY.class z) ≡ HX.class (R-cycle z)
    δ-cycle-β z =
      cong (fst (chainComplexMap→HomologyMap (presentation-map P.B) 1) ∘ fst (M.δ 1))
        (chain-cycle-β Q.χ-chain 2 z)
      ∙ cong (fst (chainComplexMap→HomologyMap (presentation-map P.B) 1))
          (M.δ-β 1 (χ-cycle z))
      ∙ chain-cycle-β (presentation-map P.B) 1 (fst (M.projection 1) (χ-cycle z))
