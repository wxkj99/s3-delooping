{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Comparison where

-- Map-compatible cellular chain comparisons for geometric pushouts.
-- The input retains a full chain equivalence and the actual span maps;
-- PrismChains.Packaging supplies it for finite CW spans.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.ChainComplex using (CW-AugChainComplex)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃ ; cellular-map)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Maps
open import DeloopS3.Bridge.DMCExactness.Exactness
open import DeloopS3.Bridge.DMCExactness.Transport

open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)

abstract
  chain-homology-map : {X Y : ChainComplex ℓ-zero} → ChainComplexMap X Y
    → (n : ℕ) → GroupHom (homology n X) (homology n Y)
  chain-homology-map {X} {Y} u n = chainComplexMap→HomologyMap {C = X} {D = Y} u n

  -- The abstract wrapper equals the library's induced homology map;
  -- this is definitional inside the owning abstract scope.
  chain-homology-map-agrees : {X Y : ChainComplex ℓ-zero} (u : ChainComplexMap X Y)
    (n : ℕ) → chain-homology-map {X} {Y} u n
             ≡ chainComplexMap→HomologyMap {C = X} {D = Y} u n
  chain-homology-map-agrees u n = refl

-- The input includes a CW model of the pushout and its chain equivalence
-- with the normalized cone. The source/vertex squares identify the induced
-- homology maps with the actual span maps, beyond group isomorphisms alone.
record ComparisonData (HA HB HC HP : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HB n) (HC n)))
  (vertices : (n : ℕ) → fst (DirProd (HB n) (HC n)) → fst (HP n)) : Type₁ where
  field
    modelE : AbGroup ℓ-zero
    modelA modelB modelC : Augmented modelE
    modelF : AugmentedMap modelA modelB
    modelG : AugmentedMap modelA modelC
    pushoutSkel : CWskel ℓ-zero
  module M = ConeMaps modelA modelB modelC modelF modelG
  field
    pushout-chains : CW-AugChainComplex pushoutSkel ≃Chain M.D
    eA : (n : ℕ) → GroupEquiv (M.HA.H n) (HA n)
    eB : (n : ℕ) → GroupEquiv (M.HB.H n) (HB n)
    eC : (n : ℕ) → GroupEquiv (M.HC.H n) (HC n)
    realisation-H : (n : ℕ)
      → GroupEquiv (homology n (CW-AugChainComplex pushoutSkel)) (HP n)

    -- Keep the homology comparison opaque as input. The following square
    -- identifies it with the supplied ACTUAL chain comparison; it is not
    -- an unrelated isomorphism of homology groups.
    eP : (n : ℕ) → GroupEquiv (M.HD.H n) (HP n)
    eP-compatible : (n : ℕ) (x : fst (homology n (CW-AugChainComplex pushoutSkel)))
      → equivFun (fst (eP n))
          (fst (chain-homology-map {X = CW-AugChainComplex pushoutSkel} {Y = M.D} (fst pushout-chains) n) x)
       ≡ equivFun (fst (realisation-H n)) x

  eTarget : (n : ℕ) → GroupEquiv (AbGroup→Group (M.target n)) (DirProd (HB n) (HC n))
  eTarget n = productEquiv {G = M.HB.H n} {H = M.HC.H n}
    {G′ = HB n} {H′ = HC n} (eB n) (eC n)

  field
    source-square : (n : ℕ) (a : fst (M.HA.H n))
      → equivFun (fst (eTarget n)) (fst (M.spanH n) a)
       ≡ source n (equivFun (fst (eA n)) a)
    vertices-square : (n : ℕ) (x : fst (M.target n))
      → equivFun (fst (eP n)) (fst (M.sumH n) x)
       ≡ vertices n (equivFun (fst (eTarget n)) x)

module _ (HA HB HC HP : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HB n) (HC n)))
  (vertices : (n : ℕ) → fst (DirProd (HB n) (HC n)) → fst (HP n))
  (comparison : ComparisonData HA HB HC HP source vertices) where
  private
    module Q = ComparisonData comparison
    module Ex = ConeExactness Q.modelA Q.modelB Q.modelC Q.modelF Q.modelG

  abstract
    comparison→sequence : SpanSequenceData HA HB HC HP source vertices
    SpanSequenceData.source-map comparison→sequence n =
      conjugateHom {G = Q.M.HA.H n} {H = AbGroup→Group (Q.M.target n)}
        {G′ = HA n} {H′ = DirProd (HB n) (HC n)} (Q.eA n) (Q.eTarget n) (Q.M.spanH n)
    SpanSequenceData.sum-map comparison→sequence n =
      conjugateHom {G = AbGroup→Group (Q.M.target n)} {H = Q.M.HD.H n}
        {G′ = DirProd (HB n) (HC n)} {H′ = HP n} (Q.eTarget n) (Q.eP n) (Q.M.sumH n)
    SpanSequenceData.source-agrees comparison→sequence n a =
      Q.source-square n (invEq (fst (Q.eA n)) a)
        ∙ cong (source n) (secEq (fst (Q.eA n)) a)
    SpanSequenceData.sum-agrees comparison→sequence n x =
      Q.vertices-square n (invEq (fst (Q.eTarget n)) x)
        ∙ cong (vertices n) (secEq (fst (Q.eTarget n)) x)
    SpanSequenceData.boundary comparison→sequence n =
      conjugateHom {G = Q.M.HD.H (suc n)} {H = Q.M.HA.H n}
        {G′ = HP (suc n)} {H′ = HA n} (Q.eP (suc n)) (Q.eA n) (Q.M.δ n)
    SpanSequenceData.exact-total comparison→sequence n _ =
      conjugate-exact {G = AbGroup→Group (Q.M.target (suc n))} {H = Q.M.HD.H (suc n)} {K = Q.M.HA.H n}
        {G′ = DirProd (HB (suc n)) (HC (suc n))} {H′ = HP (suc n)} {K′ = HA n}
        (Q.eTarget (suc n)) (Q.eP (suc n)) (Q.eA n)
        (Q.M.sumH (suc n)) (Q.M.δ n) (Ex.exact-total n)
    SpanSequenceData.exact-source comparison→sequence n _ =
      conjugate-exact {G = Q.M.HD.H (suc n)} {H = Q.M.HA.H n} {K = AbGroup→Group (Q.M.target n)}
        {G′ = HP (suc n)} {H′ = HA n} {K′ = DirProd (HB n) (HC n)}
        (Q.eP (suc n)) (Q.eA n) (Q.eTarget n)
        (Q.M.δ n) (Q.M.spanH n) (Ex.exact-source n)
    SpanSequenceData.exact-target comparison→sequence n _ =
      conjugate-exact {G = Q.M.HA.H n} {H = AbGroup→Group (Q.M.target n)} {K = Q.M.HD.H n}
        {G′ = HA n} {H′ = DirProd (HB n) (HC n)} {K′ = HP n}
        (Q.eA n) (Q.eTarget n) (Q.eP n)
        (Q.M.spanH n) (Q.M.sumH n) (Ex.exact-target n)

    -- Defining equation for this specified comparison; no uniqueness of
    -- ComparisonData or naturality of its boundary is asserted here.
    comparison→sequence-boundary-β : (n : ℕ)
      → SpanSequenceData.boundary comparison→sequence n
       ≡ conjugateHom {G = Q.M.HD.H (suc n)} {H = Q.M.HA.H n}
           {G′ = HP (suc n)} {H′ = HA n}
           (Q.eP (suc n)) (Q.eA n) (Q.M.δ n)
    comparison→sequence-boundary-β n = refl
