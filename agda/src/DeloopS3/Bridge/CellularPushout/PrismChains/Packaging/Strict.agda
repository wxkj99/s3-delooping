{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.ChainComplex
open import Cubical.CW.Homology.Base
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.CellularPushout.PrismChains.Map
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Signature
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
open import DeloopS3.Bridge.DMCExactness.Maps
open import DeloopS3.Bridge.DMCExactness.Comparison
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.DMCExactness.Conditional

open ChainComplexMap
open IsGroupHom

module Strict (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C))
  (triangular : TriangularChains A B C f g) where
  private
    module PM = PrismMap A B C f g
    module CP = PM.CP
    module P = CP.P
    module T = TriangularChains triangular
  module M = ConeMaps (CW-augmented P.B) (CW-augmented P.C) (CW-augmented P.D)
    (cellular-augmented-map P.f) (cellular-augmented-map P.g)

  Aᶜʷ Bᶜʷ Cᶜʷ Pᶜʷ : CW₀
  Aᶜʷ = realisedCW P.B
  Bᶜʷ = realisedCW P.C
  Cᶜʷ = realisedCW P.D
  f∞ : fst Aᶜʷ → fst Bᶜʷ
  f∞ = realiseCellMap P.f
  g∞ : fst Aᶜʷ → fst Cᶜʷ
  g∞ = realiseCellMap P.g
  Pᶜʷ = Pushout f∞ g∞ , PT.∣ P.hasCWskelPushout ∣₁

  abstract
    eA : (n : ℕ) → GroupEquiv (M.HA.H n) (H̃ᶜʷ Aᶜʷ n)
    eA n = GroupIso→GroupEquiv (chainComplexEquiv→HomoglogyIso (presentation-equiv P.B) n)
    eB : (n : ℕ) → GroupEquiv (M.HB.H n) (H̃ᶜʷ Bᶜʷ n)
    eB n = GroupIso→GroupEquiv (chainComplexEquiv→HomoglogyIso (presentation-equiv P.C) n)
    eC : (n : ℕ) → GroupEquiv (M.HC.H n) (H̃ᶜʷ Cᶜʷ n)
    eC n = GroupIso→GroupEquiv (chainComplexEquiv→HomoglogyIso (presentation-equiv P.D) n)
    realisation-H : (n : ℕ)
      → GroupEquiv (homology n PM.actual) (H̃ᶜʷ Pᶜʷ n)
    realisation-H n = idGroupEquiv

    f-homology : (n : ℕ)
      → cellular-map Aᶜʷ Bᶜʷ n f∞ ≡ chainComplexMap→HomologyMap (cellular-chain P.f) n
    f-homology n = cellular-map-agrees Aᶜʷ Bᶜʷ n f∞
      ∙ cellular-homology-β P.f n
    g-homology : (n : ℕ)
      → cellular-map Aᶜʷ Cᶜʷ n g∞ ≡ chainComplexMap→HomologyMap (cellular-chain P.g) n
    g-homology n = cellular-map-agrees Aᶜʷ Cᶜʷ n g∞
      ∙ cellular-homology-β P.g n

    vertexB-chain-agrees : cellular-chain CP.vertexB-cell ≡ PM.vertexB-chain
    vertexB-chain-agrees = ChainComplexMap≡ λ
      { zero → GroupHom≡ refl ; (suc n) → GroupHom≡ refl }
    vertexC-chain-agrees : cellular-chain CP.vertexC-cell ≡ PM.vertexC-chain
    vertexC-chain-agrees = ChainComplexMap≡ λ
      { zero → GroupHom≡ refl ; (suc n) → GroupHom≡ refl }

    vertexB-homology : (n : ℕ)
      → H̃ˢᵏᵉˡ→ {C = P.C} {D = P.pushoutSkel} n CP.vertexB
       ≡ chainComplexMap→HomologyMap PM.vertexB-chain n
    vertexB-homology n = approximation-homology-β CP.vertexB-cell CP.vertexB n
      (CP.vertexB-approx (suc (suc n))) refl
      ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexB-chain-agrees
    vertexC-homology : (n : ℕ)
      → H̃ˢᵏᵉˡ→ {C = P.D} {D = P.pushoutSkel} n CP.vertexC
       ≡ chainComplexMap→HomologyMap PM.vertexC-chain n
    vertexC-homology n = approximation-homology-β CP.vertexC-cell CP.vertexC n
      (CP.vertexC-approx (suc (suc n))) refl
      ∙ cong (λ h → chainComplexMap→HomologyMap h n) vertexC-chain-agrees

    actual-inl : (n : ℕ)
      → cellular-map Bᶜʷ Pᶜʷ n (transport refl ∘ inl)
       ≡ chainComplexMap→HomologyMap PM.vertexB-chain n
    actual-inl n = cong (cellular-map Bᶜʷ Pᶜʷ n)
      (funExt λ x → transportRefl (inl x))
      ∙ cellular-map-agrees Bᶜʷ Pᶜʷ n inl
      ∙ vertexB-homology n
    actual-inr : (n : ℕ)
      → cellular-map Cᶜʷ Pᶜʷ n (transport refl ∘ inr)
       ≡ chainComplexMap→HomologyMap PM.vertexC-chain n
    actual-inr n = cong (cellular-map Cᶜʷ Pᶜʷ n)
      (funExt λ x → transportRefl (inr x))
      ∙ cellular-map-agrees Cᶜʷ Pᶜʷ n inr
      ∙ vertexC-homology n

    model-vertexB-chain-square :
      compChainMap M.M.inclB PM.q-chain
       ≡ compChainMap (presentation-map P.C) PM.vertexB-chain
    model-vertexB-chain-square = ChainComplexMap≡ λ
      { zero → GroupHom≡ (cong fst (PM.q-inclB zero))
      ; (suc zero) → GroupHom≡ (cong fst (PM.q-inclB (suc zero)))
      ; (suc (suc n)) → GroupHom≡ (cong fst (PM.q-inclB (suc (suc n)))) }

    model-vertexC-chain-square :
      compChainMap M.M.inclC PM.q-chain
       ≡ compChainMap (presentation-map P.D) PM.vertexC-chain
    model-vertexC-chain-square = ChainComplexMap≡ λ
      { zero → GroupHom≡ (cong fst (PM.q-inclC zero))
      ; (suc zero) → GroupHom≡ (cong fst (PM.q-inclC (suc zero)))
      ; (suc (suc n)) → GroupHom≡ (cong fst (PM.q-inclC (suc (suc n)))) }

    eP : (n : ℕ) → GroupEquiv (M.HD.H n) (H̃ᶜʷ Pᶜʷ n)
    eP n = GroupIso→GroupEquiv (chainComplexEquiv→HomoglogyIso T.q-equivalence n)

    eP-compatible : (n : ℕ) (x : fst (homology n PM.actual))
      → equivFun (fst (eP n))
          (fst (chain-homology-map (fst T.pushout-chains) n) x)
       ≡ equivFun (fst (realisation-H n)) x
    eP-compatible n x = cong (equivFun (fst (eP n)))
      (funExt⁻ (cong fst (chain-homology-map-agrees (fst T.pushout-chains) n)) x)
      ∙ Iso.sec (fst (chainComplexEquiv→HomoglogyIso T.q-equivalence n)) x

    source-f-square : (n : ℕ) (a : fst (M.HA.H n))
      → equivFun (fst (eB n)) (fst (M.fH n) a)
       ≡ fst (cellular-map Aᶜʷ Bᶜʷ n f∞) (equivFun (fst (eA n)) a)
    source-f-square n a = homology-square
      (augmentMap (cellular-augmented-map P.f)) (presentation-map P.C)
      (presentation-map P.B) (cellular-chain P.f) (presentation-natural P.f) n a
      ∙ sym (funExt⁻ (cong fst (f-homology n)) (equivFun (fst (eA n)) a))

    source-g-square : (n : ℕ) (a : fst (M.HA.H n))
      → equivFun (fst (eC n)) (fst (M.gH n) a)
       ≡ fst (cellular-map Aᶜʷ Cᶜʷ n g∞) (equivFun (fst (eA n)) a)
    source-g-square n a = homology-square
      (augmentMap (cellular-augmented-map P.g)) (presentation-map P.D)
      (presentation-map P.B) (cellular-chain P.g) (presentation-natural P.g) n a
      ∙ sym (funExt⁻ (cong fst (g-homology n)) (equivFun (fst (eA n)) a))

    vertexB-square : (n : ℕ) (b : fst (M.HB.H n))
      → equivFun (fst (eP n)) (fst (M.M.H̃inclB n) b)
       ≡ fst (cellular-map Bᶜʷ Pᶜʷ n (transport refl ∘ inl))
          (equivFun (fst (eB n)) b)
    vertexB-square n b = homology-square M.M.inclB PM.q-chain
      (presentation-map P.C) PM.vertexB-chain model-vertexB-chain-square n b
      ∙ sym (funExt⁻ (cong fst (actual-inl n)) (equivFun (fst (eB n)) b))

    vertexC-square : (n : ℕ) (c : fst (M.HC.H n))
      → equivFun (fst (eP n)) (fst (M.M.H̃inclC n) c)
       ≡ fst (cellular-map Cᶜʷ Pᶜʷ n (transport refl ∘ inr))
          (equivFun (fst (eC n)) c)
    vertexC-square n c = homology-square M.M.inclC PM.q-chain
      (presentation-map P.D) PM.vertexC-chain model-vertexC-chain-square n c
      ∙ sym (funExt⁻ (cong fst (actual-inr n)) (equivFun (fst (eC n)) c))

    source-square : (n : ℕ) (a : fst (M.HA.H n))
      → (equivFun (fst (eB n)) (fst (fst (M.spanH n) a)) ,
          equivFun (fst (eC n)) (snd (fst (M.spanH n) a)))
       ≡ actual-source Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ n (equivFun (fst (eA n)) a)
    source-square n a = ΣPathP (source-f-square n a ,
      presinv (snd (eC n)) (fst (M.gH n) a)
        ∙ cong (GroupStr.inv (snd (H̃ᶜʷ Cᶜʷ n))) (source-g-square n a))

    vertices-square : (n : ℕ) (x : fst (M.target n))
      → equivFun (fst (eP n)) (fst (M.sumH n) x)
       ≡ actual-sum Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ refl n
          (equivFun (fst (eB n)) (fst x) , equivFun (fst (eC n)) (snd x))
    vertices-square n (b , c) = pres· (snd (eP n)) _ _
      ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ Pᶜʷ n))) (vertexB-square n b) (vertexC-square n c)

    comparison : ComparisonData
      (H̃ᶜʷ Aᶜʷ) (H̃ᶜʷ Bᶜʷ) (H̃ᶜʷ Cᶜʷ) (H̃ᶜʷ Pᶜʷ)
      (actual-source Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞)
      (actual-sum Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ refl)
    ComparisonData.modelE comparison = ℤ[Fin 1 ]
    ComparisonData.modelA comparison = CW-augmented P.B
    ComparisonData.modelB comparison = CW-augmented P.C
    ComparisonData.modelC comparison = CW-augmented P.D
    ComparisonData.modelF comparison = cellular-augmented-map P.f
    ComparisonData.modelG comparison = cellular-augmented-map P.g
    ComparisonData.pushoutSkel comparison = P.pushoutSkel
    ComparisonData.pushout-chains comparison = T.pushout-chains
    ComparisonData.eA comparison = eA
    ComparisonData.eB comparison = eB
    ComparisonData.eC comparison = eC
    ComparisonData.realisation-H comparison = realisation-H
    ComparisonData.eP comparison = eP
    ComparisonData.eP-compatible comparison = eP-compatible
    ComparisonData.source-square comparison = source-square
    ComparisonData.vertices-square comparison = vertices-square

    strict-comparison : PushoutChainsComparison Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ
    strict-comparison = refl , comparison , snd P.hasCWskelPushout

    strict-pushoutLES : GeometricPushoutLES Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ
    strict-pushoutLES = comparison→LES Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ strict-comparison

    -- The boundary of THIS packaged LES uses the specified inverse-q
    -- comparison, followed by DMC projection and the fixed presentation.
    strict-boundary-β : (n : ℕ)
      → SpanSequenceData.boundary (snd strict-pushoutLES) n
       ≡ compGroupHom
           (chainComplexMap→HomologyMap (fst T.pushout-chains) (suc n))
           (compGroupHom (M.δ n)
             (chainComplexMap→HomologyMap (presentation-map P.B) n))
    strict-boundary-β n =
      comparison→LES-boundary-β Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ strict-comparison n
      ∙ comparison→sequence-boundary-β
          (H̃ᶜʷ Aᶜʷ) (H̃ᶜʷ Bᶜʷ) (H̃ᶜʷ Cᶜʷ) (H̃ᶜʷ Pᶜʷ)
          (actual-source Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞)
          (actual-sum Aᶜʷ Bᶜʷ Cᶜʷ f∞ g∞ Pᶜʷ refl) comparison n
      ∙ GroupHom≡ refl
