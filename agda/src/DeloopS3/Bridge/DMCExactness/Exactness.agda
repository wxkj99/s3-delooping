{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Exactness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Maps
open import DeloopS3.Bridge.DMCExactness.Cycles

abstract
  exact-from-kernel : {G H K : Group₀} (u : GroupHom G H) (v : GroupHom H K)
    → ((h : fst H) → fst v h ≡ GroupStr.1g (snd K) → PT.∥ fiber (fst u) h ∥₁)
    → ((x : fst G) → fst v (fst u x) ≡ GroupStr.1g (snd K))
    → Exact₃ u v
  exact-from-kernel {K = K} u v ker composite h = propBiimpl→Equiv
    (GroupStr.is-set (snd K) _ _) PT.isPropPropTrunc (ker h)
    (PT.rec (GroupStr.is-set (snd K) _ _) λ { (x , p) → sym (cong (fst v) p) ∙ composite x })

module ConeExactness {E : AbGroup ℓ-zero} (A B C : Augmented E)
  (f : AugmentedMap A B) (g : AugmentedMap A C) where
  open ConeMaps A B C f g
  open CycleAdjustments A B C f g

  abstract
    exact-total : (n : ℕ) → Exact₃ (sumH (suc n)) (δ n)
    exact-total n = exact-from-kernel (sumH (suc n)) (δ n)
      (SQ.elimProp (λ _ → isPropΠ λ _ → PT.isPropPropTrunc) (total-kernel-cycle n))
      (λ { (b , c) → SQ.elimProp2
        {P = λ b c → fst (δ n) (fst (sumH (suc n)) (b , c)) ≡ HA.H.1g n}
        (λ _ _ → HA.H.is-set n _ _) (total-composite-cycle n) b c })

    exact-source : (n : ℕ) → Exact₃ (δ n) (spanH n)
    exact-source n = exact-from-kernel (δ n) (spanH n)
      (SQ.elimProp (λ _ → isPropΠ λ _ → PT.isPropPropTrunc) (source-kernel-cycle n))
      (SQ.elimProp (λ _ → AbGroupStr.is-set (snd (target n)) _ _) (source-composite-cycle n))

    exact-target : (n : ℕ) → Exact₃ (spanH n) (sumH n)
    exact-target n = exact-from-kernel (spanH n) (sumH n)
      (λ { (b , c) → SQ.elimProp2
        {P = λ b c → fst (sumH n) (b , c) ≡ HD.H.1g n
          → PT.∥ fiber (fst (spanH n)) (b , c) ∥₁}
        (λ _ _ → isPropΠ λ _ → PT.isPropPropTrunc) (target-kernel-cycle n) b c })
      (SQ.elimProp (λ _ → HD.H.is-set n _ _) (target-composite-cycle n))
