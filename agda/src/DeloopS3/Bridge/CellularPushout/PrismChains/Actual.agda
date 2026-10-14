{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Actual where

-- Actual continuous vertex maps, with the explicit triangular inverse.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Comparison
open import DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFree
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
  using (cellular-chain ; approximation-homology-β)

module ActualVertices (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module Q = Comparison A B C f g
    module E = Q.Complete finite-free-direct-finite
    module CP = Q.CP
    module P = CP.P

  abstract
    vertexB-chain-agrees : cellular-chain CP.vertexB-cell ≡ Q.vertexB-chain
    vertexB-chain-agrees = ChainComplexMap≡ λ
      { zero → GroupHom≡ refl ; (suc n) → GroupHom≡ refl }

    vertexC-chain-agrees : cellular-chain CP.vertexC-cell ≡ Q.vertexC-chain
    vertexC-chain-agrees = ChainComplexMap≡ λ
      { zero → GroupHom≡ refl ; (suc n) → GroupHom≡ refl }

    vertexB-homology-actual : (n : ℕ)
      → H̃ˢᵏᵉˡ→ {C = P.C} {D = P.pushoutSkel} n CP.vertexB
       ≡ chainComplexMap→HomologyMap Q.vertexB-chain n
    vertexB-homology-actual n =
      approximation-homology-β CP.vertexB-cell CP.vertexB n
        (CP.vertexB-approx (suc (suc n))) refl
      ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexB-chain-agrees

    vertexC-homology-actual : (n : ℕ)
      → H̃ˢᵏᵉˡ→ {C = P.D} {D = P.pushoutSkel} n CP.vertexC
       ≡ chainComplexMap→HomologyMap Q.vertexC-chain n
    vertexC-homology-actual n =
      approximation-homology-β CP.vertexC-cell CP.vertexC n
        (CP.vertexC-approx (suc (suc n))) refl
      ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexC-chain-agrees

    vertexB-Hβ : (n : ℕ)
      → compGroupHom (H̃ˢᵏᵉˡ→ {C = P.C} {D = P.pushoutSkel} n CP.vertexB)
          (chainComplexMap→HomologyMap E.χ-chain n)
       ≡ chainComplexMap→HomologyMap CP.inclB n
    vertexB-Hβ n = cong
      (λ h → compGroupHom h (chainComplexMap→HomologyMap E.χ-chain n))
      (vertexB-homology-actual n) ∙ E.vertexB-homology n

    vertexC-Hβ : (n : ℕ)
      → compGroupHom (H̃ˢᵏᵉˡ→ {C = P.D} {D = P.pushoutSkel} n CP.vertexC)
          (chainComplexMap→HomologyMap E.χ-chain n)
       ≡ chainComplexMap→HomologyMap CP.inclC n
    vertexC-Hβ n = cong
      (λ h → compGroupHom h (chainComplexMap→HomologyMap E.χ-chain n))
      (vertexC-homology-actual n) ∙ E.vertexC-homology n
