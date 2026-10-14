{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.SeifertChains.Seifert where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Bridge.SeifertChains.Block
open import DeloopS3.Bridge.SeifertChains.Matrices

module Seifert (p q r : ℤ) where
  module B = Blocks ℤAbGroup ℤ² ℤ³ ℤ⁶ sum₃ D (Araw p q r)
  module Top = NoIncoming B.K 3 (λ _ → refl)

  -- Ordinary ranks 4,9,8,3,0; augmented ranks 1,4,9,8,3,0.
  -- Degree-one coordinates: ((a,b),(h,c₁,c₂,c₃)), then three vertex prisms.
  -- Degree-two coordinates: (a×h,b×h), then (u₁,u₂,u₃,h₁,h₂,h₃).
  K : ChainComplex ℓ-zero
  K = B.K

  ones-cycle : fst (ker∂n 3 K)
  ones-cycle = (pos 1 , pos 1 , pos 1) , ΣPathP (D-diagonal (pos 1) , refl)

  ones-class : fst (homology 3 K)
  ones-class = SQ.[ ones-cycle ]

  abstract
    H₃ : GroupEquiv (homology 3 K) ℤGroup
    H₃ = compGroupEquiv Top.H-to-cycle (compGroupEquiv B.top-cycles D-kernel)

    H₃-ones-coordinate : equivFun (fst H₃) ones-class ≡ pos 1
    H₃-ones-coordinate =
      cong (λ z → snd (snd (fst (equivFun (fst B.top-cycles) z))))
        (Top.H-to-cycle-class ones-cycle)
      ∙ cong (λ v → snd (snd v)) (B.top-cycles-coordinate ones-cycle)

    H₃-ones : invEq (fst H₃) (pos 1) ≡ ones-class
    H₃-ones = cong (invEq (fst H₃)) (sym H₃-ones-coordinate)
      ∙ retEq (fst H₃) ones-class

    H₂-zero : ((x : ℤ) → q Z.· x ≡ pos 0 → x ≡ pos 0)
      → ((x : ℤ) → determinant p q r Z.· x ≡ pos 0 → x ≡ pos 0)
      → isContr (fst (homology 2 K))
    H₂-zero cancel-q cancel-det = B.H₂-zero (fst D-section) D-split
      (Araw-kernel p q r cancel-q cancel-det)

seifertK : (p q r : ℤ) → ChainComplex ℓ-zero
seifertK = Seifert.K

seifert-H₃ : (p q r : ℤ) → GroupEquiv (homology 3 (seifertK p q r)) ℤGroup
seifert-H₃ = Seifert.H₃

seifert-ones-cycle : (p q r : ℤ) → fst (ker∂n 3 (seifertK p q r))
seifert-ones-cycle = Seifert.ones-cycle

seifert-ones-class : (p q r : ℤ) → fst (homology 3 (seifertK p q r))
seifert-ones-class = Seifert.ones-class

seifert-H₃-ones : (p q r : ℤ)
  → invEq (fst (seifert-H₃ p q r)) (pos 1) ≡ seifert-ones-class p q r
seifert-H₃-ones = Seifert.H₃-ones

abstract
  positive-cancel : (n : ℕ) (x : ℤ) → pos (suc n) Z.· x ≡ pos 0 → x ≡ pos 0
  positive-cancel n x eq = Z.·suc→0 x n (Z.·Comm x (pos (suc n)) ∙ eq)

  -- A sufficient hypothesis without division; zero-determinant cases
  -- are excluded. The four instances in Cases satisfy this hypothesis.
  seifert-H₂-zero : (p q r : ℤ) → (q ≡ pos 0 → ⊥)
    → (determinant p q r ≡ pos 0 → ⊥)
    → isContr (fst (homology 2 (seifertK p q r)))
  seifert-H₂-zero p q r q≠0 det≠0 = Seifert.H₂-zero p q r
    (λ x eq → Z.isIntegralℤ q x eq q≠0)
    (λ x eq → Z.isIntegralℤ (determinant p q r) x eq det≠0)
