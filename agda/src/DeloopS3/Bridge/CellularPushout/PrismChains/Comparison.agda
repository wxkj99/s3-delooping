{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Finite
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.ChainComplex
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.CellGroups using (module Split₃Inclusions)
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction using (module PrismRetraction)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Map
open import DeloopS3.Bridge.CellularPushout.PrismChains.Triangular

open ChainComplex
open ChainComplexMap
open finChainComplexMap
open IsGroupHom

-- Isolate the one generic algebraic dependency from all geometry.
FiniteFreeCancellation : Type
FiniteFreeCancellation = (n : ℕ) (u t : AbGroupHom ℤ[Fin n ] ℤ[Fin n ])
  → compGroupHom u t ≡ idGroupHom → compGroupHom t u ≡ idGroupHom

module Comparison (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  open PrismMap A B C f g public
  open Seam A B C f g using (X ; Y ; YB ; YC ; K ; VB ; VC)
  open PrismRetraction A B C f g using (R ; R-K ; R-VB ; R-VC)

  module T (n : ℕ) = Triangular
    (Z YB (suc n)) (Z YC (suc n)) (Z X n) (Z Y (suc n))
    (CP.pushout-cell-groups (suc (suc n))) (VB (suc n)) (VC (suc n)) (K n) (R n)
    (CP.vertexB-coordinates₊ n) (CP.vertexC-coordinates₊ n)
    (R-K n) (R-VB n) (R-VC n)

  χ : (i : ℕ) → AbGroupHom (chain actual i) (chain CP.DMC i)
  χ zero = idGroupHom
  χ (suc zero) = CP.pushout-cell-map 1
  χ (suc (suc n)) = T.χ n

  abstract
    χq₀ : compGroupHom (q 1) (χ 1) ≡ idGroupHom
    χq₀ = GroupHom≡ (funExt λ (b , c) → pres· (snd (χ 1)) (fst (VB 0) b) (fst (VC 0) c)
      ∙ cong₂ (AbGroupStr._+_ (snd (chain CP.DMC 1)))
        (funExt⁻ (cong fst CP.vertexB-coordinates₀) b)
        (funExt⁻ (cong fst CP.vertexC-coordinates₀) c)
      ∙ ΣPathP (AbGroupStr.+IdR (snd (Z YB 0)) b , AbGroupStr.+IdL (snd (Z YC 0)) c))

    qχ₀ : compGroupHom (χ 1) (q 1) ≡ idGroupHom
    qχ₀ = GroupHom≡ (funExt λ z →
      sym (retEq (fst (CP.pushout-cell-groups 1)) (fst (q 1) (fst (χ 1) z)))
      ∙ cong (invEq (fst (CP.pushout-cell-groups 1))) (funExt⁻ (cong fst χq₀) (fst (χ 1) z))
      ∙ retEq (fst (CP.pushout-cell-groups 1)) z)

    χq : (i : ℕ) → compGroupHom (q i) (χ i) ≡ idGroupHom
    χq zero = GroupHom≡ refl
    χq (suc zero) = χq₀
    χq (suc (suc n)) = T.χq n

    χ-vertexB : (i : ℕ)
      → compGroupHom (chainmap vertexB-chain i) (χ i) ≡ chainmap CP.inclB i
    χ-vertexB zero = GroupHom≡ refl
    χ-vertexB (suc zero) = CP.vertexB-coordinates₀
    χ-vertexB (suc (suc n)) = T.χ-jB n

    χ-vertexC : (i : ℕ)
      → compGroupHom (chainmap vertexC-chain i) (χ i) ≡ chainmap CP.inclC i
    χ-vertexC zero = GroupHom≡ refl
    χ-vertexC (suc zero) = CP.vertexC-coordinates₀
    χ-vertexC (suc (suc n)) = T.χ-jC n

  -- The LES relative coordinate is unchanged by the triangular mixing.
  χ-relative : (n : ℕ)
    → compGroupHom (χ (suc (suc n))) (T.pA n) ≡ R n
  χ-relative n = GroupHom≡ refl

  -- This module takes ONLY finite free direct finiteness, not a support
  -- equation or a geometric comparison hypothesis.
  module Complete (finite-free-direct-finite : FiniteFreeCancellation) where
    private
      module E (n : ℕ) = T.Complete n (finite-free-direct-finite (snd Y .fst (suc n)))

    qχ : (i : ℕ) → compGroupHom (χ i) (q i) ≡ idGroupHom
    qχ zero = GroupHom≡ refl
    qχ (suc zero) = qχ₀
    qχ (suc (suc n)) = E.qχ n

    prism-block : (n : ℕ) → AbGroupHom (Z X n) (Z X n)
    prism-block n = compGroupHom (K n) (compGroupHom (T.s n) (T.pA n))

    prism-block-inverse : (n : ℕ) → AbGroupHom (Z X n) (Z X n)
    prism-block-inverse n = compGroupHom (CP.JA n) (R n)

    abstract
      prism-block-R : (n : ℕ)
        → compGroupHom (R n) (prism-block n) ≡ compGroupHom (T.s n) (T.pA n)
      prism-block-R n = GroupHom≡ (funExt λ z →
        sym (cong (λ w → snd (snd w))
          (T.sq n (fst (fst (χ (suc (suc n))) z))
            (fst (snd (fst (χ (suc (suc n))) z))) (fst (R n) z)))
        ∙ cong (λ w → snd (snd (fst (T.s n) w)))
          (funExt⁻ (cong fst (qχ (suc (suc n)))) z))

      prism-block-section : (n : ℕ)
        → compGroupHom (prism-block-inverse n) (prism-block n) ≡ idGroupHom
      prism-block-section n = GroupHom≡ (funExt λ a →
        funExt⁻ (cong fst (prism-block-R n)) (fst (CP.JA n) a)
        ∙ cong (λ w → snd (snd w))
          (funExt⁻ (cong fst (Split₃Inclusions.split-A
            (snd YB .fst (suc n)) (snd X .fst n) (snd YC .fst (suc n)))) a))

      prism-block-retraction : (n : ℕ)
        → compGroupHom (prism-block n) (prism-block-inverse n) ≡ idGroupHom
      prism-block-retraction n = finite-free-direct-finite (snd X .fst n)
        (prism-block-inverse n) (prism-block n) (prism-block-section n)

    prism-block-Iso : (n : ℕ) → Iso (fst (Z X n)) (fst (Z X n))
    Iso.fun (prism-block-Iso n) = fst (prism-block n)
    Iso.inv (prism-block-Iso n) = fst (prism-block-inverse n)
    Iso.sec (prism-block-Iso n) = funExt⁻ (cong fst (prism-block-section n))
    Iso.ret (prism-block-Iso n) = funExt⁻ (cong fst (prism-block-retraction n))

    prism-block-equiv : (n : ℕ) → AbGroupEquiv (Z X n) (Z X n)
    prism-block-equiv n = isoToEquiv (prism-block-Iso n) , snd (prism-block n)

    abstract
      χ-boundary : (i : ℕ)
        → compGroupHom (χ (suc i)) (bdry CP.DMC i)
         ≡ compGroupHom (bdry actual i) (χ i)
      χ-boundary i = GroupHom≡ (funExt λ z → sym
        (cong (λ w → fst (χ i) (fst (bdry actual i) w))
          (sym (funExt⁻ (cong fst (qχ (suc i))) z))
        ∙ cong (fst (χ i))
          (funExt⁻ (cong fst (bdrycomm q-chain i)) (fst (χ (suc i)) z))
        ∙ funExt⁻ (cong fst (χq i)) (fst (bdry CP.DMC i) (fst (χ (suc i)) z))))

    χ-chain : ChainComplexMap actual CP.DMC
    chainmap χ-chain = χ
    bdrycomm χ-chain = χ-boundary

    χIso : (i : ℕ) → Iso (fst (chain actual i)) (fst (chain CP.DMC i))
    Iso.fun (χIso i) = fst (χ i)
    Iso.inv (χIso i) = fst (q i)
    Iso.sec (χIso i) = funExt⁻ (cong fst (χq i))
    Iso.ret (χIso i) = funExt⁻ (cong fst (qχ i))

    q-is-equiv : isChainEquiv q-chain
    q-is-equiv i = snd (isoToEquiv (invIso (χIso i)))

    q-chain-equivalence : CP.DMC ≃Chain actual
    q-chain-equivalence = q-chain , q-is-equiv

    abstract
      inverse-chain-agrees : invChainMap q-chain-equivalence ≡ χ-chain
      inverse-chain-agrees = ChainComplexMap≡ λ i → GroupHom≡ refl

    pushout-chains-triangular : actual ≃Chain CP.DMC
    fst pushout-chains-triangular = χ-chain
    snd pushout-chains-triangular i = snd (isoToEquiv (χIso i))

    pushout-chains-triangular-finite : (m : ℕ) → actual ≃⟨ m ⟩Chain CP.DMC
    fchainmap (fst (pushout-chains-triangular-finite m)) i = χ (fst i)
    fbdrycomm (fst (pushout-chains-triangular-finite m)) i = χ-boundary (fst i)
    snd (pushout-chains-triangular-finite m) i = snd (isoToEquiv (χIso (fst i)))

    pushout-homology-triangular : (n : ℕ) → GroupIso (H̃ˢᵏᵉˡ Y n) (homology n CP.DMC)
    pushout-homology-triangular = chainComplexEquiv→HomoglogyIso pushout-chains-triangular

    abstract
      vertexB-triangular : compChainMap vertexB-chain χ-chain ≡ CP.inclB
      vertexB-triangular = ChainComplexMap≡ χ-vertexB

      vertexC-triangular : compChainMap vertexC-chain χ-chain ≡ CP.inclC
      vertexC-triangular = ChainComplexMap≡ χ-vertexC

      vertexB-homology : (n : ℕ)
        → compGroupHom (chainComplexMap→HomologyMap vertexB-chain n)
            (chainComplexMap→HomologyMap χ-chain n)
         ≡ chainComplexMap→HomologyMap CP.inclB n
      vertexB-homology n = sym (chainComplexMap→HomologyMapComp vertexB-chain χ-chain n)
        ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexB-triangular

      vertexC-homology : (n : ℕ)
        → compGroupHom (chainComplexMap→HomologyMap vertexC-chain n)
            (chainComplexMap→HomologyMap χ-chain n)
         ≡ chainComplexMap→HomologyMap CP.inclC n
      vertexC-homology n = sym (chainComplexMap→HomologyMapComp vertexC-chain χ-chain n)
        ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexC-triangular
