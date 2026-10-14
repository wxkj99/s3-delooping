{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ZeroNaturality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Algebra.Group using (GroupStr)
open import Cubical.Algebra.Group.MorphismProperties using (trivGroupHom)
open import Cubical.Algebra.AbGroup using (AbGroupStr)
open import Cubical.Algebra.ChainComplex.Base using (ChainComplex ; ChainComplexMap)
open import Cubical.Algebra.ChainComplex.Homology
  using (homology ; chainComplexMap→HomologyMap)
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Bridge.ComponentHomology.ZeroDifferentials
  using (zero-differentials-iso)

abstract
  zero-differentials-natural : (C D : ChainComplex ℓ-zero) (k : ℕ)
    (outC : ChainComplex.bdry C k ≡ trivGroupHom)
    (inC : ChainComplex.bdry C (suc k) ≡ trivGroupHom)
    (outD : ChainComplex.bdry D k ≡ trivGroupHom)
    (inD : ChainComplex.bdry D (suc k) ≡ trivGroupHom)
    (φ : ChainComplexMap C D)
    (x : fst (homology k C)) →
    Iso.fun (fst (zero-differentials-iso D k outD inD))
      (fst (chainComplexMap→HomologyMap φ k) x)
    ≡ fst (ChainComplexMap.chainmap φ (suc k))
      (Iso.fun (fst (zero-differentials-iso C k outC inC)) x)
  zero-differentials-natural C D k outC inC outD inD φ =
    SQ.elimProp
      (λ _ → AbGroupStr.is-set (snd (ChainComplex.chain D (suc k))) _ _)
      (λ _ → refl)
