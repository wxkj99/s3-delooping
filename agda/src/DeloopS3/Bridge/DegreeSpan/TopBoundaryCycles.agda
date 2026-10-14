{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopBoundaryCycles where

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

open ChainComplexMap
open finChainComplexMap
open IsGroupHom

chain-cycle : {C D : ChainComplex ℓ-zero} (f : ChainComplexMap C D)
  (n : ℕ) → Homology.Cycle C n → Homology.Cycle D n
chain-cycle f n (z , p) = fst (chainmap f (suc n)) z ,
  funExt⁻ (cong fst (bdrycomm f n)) z
  ∙ cong (fst (chainmap f n)) p ∙ pres1 (snd (chainmap f n))

abstract
  chain-cycle-β : {C D : ChainComplex ℓ-zero} (f : ChainComplexMap C D)
    (n : ℕ) (z : Homology.Cycle C n)
    → fst (chainComplexMap→HomologyMap f n) (Homology.class C n z)
     ≡ Homology.class D n (chain-cycle f n z)
  chain-cycle-β {D = D} f n z = Homology.class-path D n refl

finite-cycle : {C D : ChainComplex ℓ-zero} {m : ℕ}
  (f : finChainComplexMap (suc m) C D) (n : Fin m)
  → Homology.Cycle C (fst n) → Homology.Cycle D (fst n)
finite-cycle f (n , p) (z , q) =
  fst (fchainmap f (suc n , <ᵗ-trans p <ᵗsuc)) z ,
  funExt⁻ (cong fst (fbdrycomm f (n , <ᵗ-trans p <ᵗsuc))) z
  ∙ cong (fst (fchainmap f (n , _))) q
  ∙ pres1 (snd (fchainmap f (n , _)))

abstract
  finite-cycle-β : {C D : ChainComplex ℓ-zero} {m : ℕ}
    (f : finChainComplexMap (suc m) C D) (n : Fin m)
    (z : Homology.Cycle C (fst n))
    → fst (finChainComplexMap→HomologyMap m f n) (Homology.class C (fst n) z)
     ≡ Homology.class D (fst n) (finite-cycle f n z)
  finite-cycle-β {D = D} f n z = Homology.class-path D (fst n) refl

-- This is the specified triangular comparison, not an arbitrary witness of
-- ComparisonInput. Its inverse agrees with the inverse of the q
-- equivalence by Q.inverse-chain-agrees.
module SpecifiedBoundary (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where

  module Q = PC.PrismChains A B C f g
  module P = Q.CP.P
  module R = PR.PrismRetraction A B C f g
  module M = ConeMaps (CW-augmented P.B) (CW-augmented P.C) (CW-augmented P.D)
    (cellular-augmented-map P.f) (cellular-augmented-map P.g)
  module HY = Homology (CW-AugChainComplex P.pushoutSkel) 3
  module HX = Homology (CW-AugChainComplex P.B) 2

  -- Homology degree 3 uses augmented chain index 4, hence χ 4 and R 2.
  χ-cycle : HY.Cycle → M.HD.Cycle 3
  χ-cycle = chain-cycle Q.χ-chain 3

  R-cycle : HY.Cycle → HX.Cycle
  R-cycle z = chain-cycle (presentation-map P.B) 2
    (fst (M.projection 2) (χ-cycle z))

  δ : GroupHom (H̃ˢᵏᵉˡ P.pushoutSkel 3) (H̃ˢᵏᵉˡ P.B 2)
  δ = compGroupHom (chainComplexMap→HomologyMap Q.χ-chain 3)
    (compGroupHom (M.δ 2) (chainComplexMap→HomologyMap (presentation-map P.B) 2))

  δ-inverse : GroupHom (H̃ˢᵏᵉˡ P.pushoutSkel 3) (H̃ˢᵏᵉˡ P.B 2)
  δ-inverse = compGroupHom
    (chainComplexMap→HomologyMap (invChainMap Q.q-chain-equivalence) 3)
    (compGroupHom (M.δ 2)
      (chainComplexMap→HomologyMap (presentation-map P.B) 2))

  abstract
    -- The precise comparison used by strict packaging is the inverse of q.
    -- This is an equality for that specified equivalence, not uniqueness of
    -- arbitrary comparison data or geometric LES witnesses.
    δ-inverse-comparison-agrees : δ-inverse ≡ δ
    δ-inverse-comparison-agrees = cong
      (λ h → compGroupHom (chainComplexMap→HomologyMap h 3)
        (compGroupHom (M.δ 2)
          (chainComplexMap→HomologyMap (presentation-map P.B) 2)))
      Q.inverse-chain-agrees

    R-cycle-coefficient : (z : HY.Cycle) → fst (R-cycle z) ≡ fst (R.R 2) (fst z)
    R-cycle-coefficient z = funExt⁻ (cong fst (Q.χ-relative 2)) (fst z)

    δ-cycle-β : (z : HY.Cycle) → fst δ (HY.class z) ≡ HX.class (R-cycle z)
    δ-cycle-β z =
      cong (fst (chainComplexMap→HomologyMap (presentation-map P.B) 2) ∘ fst (M.δ 2))
        (chain-cycle-β Q.χ-chain 3 z)
      ∙ cong (fst (chainComplexMap→HomologyMap (presentation-map P.B) 2))
          (M.δ-β 2 (χ-cycle z))
      ∙ chain-cycle-β (presentation-map P.B) 2 (fst (M.projection 2) (χ-cycle z))
