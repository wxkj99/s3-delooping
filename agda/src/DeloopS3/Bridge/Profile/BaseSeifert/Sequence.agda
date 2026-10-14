{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.BaseSeifert.Groups

-- Group-only adapter: replace the chosen LES source by a fixed actual
-- source, using its specified equality, without unfolding H̃ᶜʷ.
module Canonical (HA HB HC HP : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HB n) (HC n)))
  (vertices : (n : ℕ) → fst (DirProd (HB n) (HC n)) → fst (HP n))
  (L : SpanSequenceData HA HB HC HP source vertices)
  (s₂ : GroupHom (HA 2) (DirProd (HB 2) (HC 2)))
  (s₁ : GroupHom (HA 1) (DirProd (HB 1) (HC 1)))
  (s₂-agrees : (a : fst (HA 2)) → fst s₂ a ≡ source 2 a)
  (s₁-agrees : (a : fst (HA 1)) → fst s₁ a ≡ source 1 a) where
  private
    module L = SpanSequenceData L

    path₂ : L.source-map 2 ≡ s₂
    path₂ = GroupHom≡ (funExt λ a → L.source-agrees 2 a ∙ sym (s₂-agrees a))
    path₁ : L.source-map 1 ≡ s₁
    path₁ = GroupHom≡ (funExt λ a → L.source-agrees 1 a ∙ sym (s₁-agrees a))

  abstract
    at-overlap₂ : Exact₃ (L.boundary 2) s₂
    at-overlap₂ = subst (Exact₃ (L.boundary 2)) path₂ (L.exact-source 2 (2 , refl))

    at-vertices₂ : Exact₃ s₂ (L.sum-map 2)
    at-vertices₂ = subst (λ s → Exact₃ s (L.sum-map 2)) path₂ (L.exact-target 2 (2 , refl))

    at-overlap₁ : Exact₃ (L.boundary 1) s₁
    at-overlap₁ = subst (Exact₃ (L.boundary 1)) path₁ (L.exact-source 1 (3 , refl))

  module Top (zeroB : isContr (fst (HB 3))) (zeroC : isContr (fst (HC 3))) where
    module K = KernelSequence (L.sum-map 3) (L.boundary 2) s₂
      (L.exact-total 2 (2 , refl)) at-overlap₂ (isContrΣ zeroB (λ _ → zeroC))
    open K public using (kernel-equiv ; kernel-equiv-coordinate)

  abstract
    H₂-zero : ((w : fst (DirProd (HB 2) (HC 2))) → PT.∥ fiber (fst s₂) w ∥₁)
      → ((a : fst (HA 1)) → fst s₁ a ≡ GroupStr.1g (snd (DirProd (HB 1) (HC 1)))
          → a ≡ GroupStr.1g (snd (HA 1)))
      → isContr (fst (HP 2))
    H₂-zero onto injective = middle-zero s₂ (L.sum-map 2) (L.boundary 1) s₁
      at-vertices₂ (L.exact-total 1 (3 , refl)) at-overlap₁ onto injective

-- The marking is the preimage of the diagonal under the MV boundary.
-- A merely-given LES only gives this oriented equivalence merely.
record DiagonalData (P A : Group₀) (eA : GroupEquiv A (AbGroup→Group ℤ³)) : Type where
  field
    boundary : GroupHom P A
    integer-equiv : GroupEquiv P ℤGroup
    diagonal-coordinate : (t : ℤ)
      → equivFun (fst eA) (fst boundary (invEq (fst integer-equiv) t)) ≡ fst diagonal t

module DiagonalKernel {P A W : Group₀}
  (δ : GroupHom P A) (s : GroupHom A W)
  (eA : GroupEquiv A (AbGroup→Group ℤ³))
  (eW : GroupEquiv W (AbGroup→Group ℤ²))
  (square : (a : fst A) → equivFun (fst eW) (fst s a) ≡ fst D (equivFun (fst eA) a))
  (eK : GroupEquiv P (kerGroup s))
  (eK-coordinate : (x : fst P) → fst (equivFun (fst eK) x) ≡ fst δ x) where

  private
    module Change = ChangeKernel eA eW s D square
    k : GroupEquiv P (kerGroup D)
    k = compGroupEquiv eK Change.kernel-change

    coordinate : (x : fst P) → fst (equivFun (fst k) x) ≡ equivFun (fst eA) (fst δ x)
    coordinate x = Change.kernel-change-coordinate (equivFun (fst eK) x)
      ∙ cong (equivFun (fst eA)) (eK-coordinate x)

  abstract
    diagonal-data : DiagonalData P A eA
    DiagonalData.boundary diagonal-data = δ
    DiagonalData.integer-equiv diagonal-data = compGroupEquiv k D-kernel
    DiagonalData.diagonal-coordinate diagonal-data t =
      sym (coordinate x)
      ∙ D-kernel-diagonal (fst (equivFun (fst k) x)) (snd (equivFun (fst k) x))
      ∙ cong (fst diagonal) (secEq (fst (compGroupEquiv k D-kernel)) t)
      where
      x : fst P
      x = invEq (fst (compGroupEquiv k D-kernel)) t

    diagonal-boundary : DiagonalData.boundary diagonal-data ≡ δ
    diagonal-boundary = refl

-- All marked-matrix reasoning is elaborated before specializing HA,...
-- to cellular homology. This boundary prevents normalization of the
-- cellular-approximation implementation at dependent record projections.
module MatrixConsequences (HA HB HC HP : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HB n) (HC n)))
  (s₂ : GroupHom (HA 2) (DirProd (HB 2) (HC 2)))
  (s₁ : GroupHom (HA 1) (DirProd (HB 1) (HC 1)))
  (s₂-agrees : (a : fst (HA 2)) → fst s₂ a ≡ source 2 a)
  (s₁-agrees : (a : fst (HA 1)) → fst s₁ a ≡ source 1 a)
  (eA₂ : GroupEquiv (HA 2) (AbGroup→Group ℤ³))
  (eW₂ : GroupEquiv (DirProd (HB 2) (HC 2)) (AbGroup→Group ℤ²))
  (eA₁ : GroupEquiv (HA 1) (AbGroup→Group ℤ⁶))
  (eW₁ : GroupEquiv (DirProd (HB 1) (HC 1)) (AbGroup→Group vertex₁))
  (zeroB : isContr (fst (HB 3))) (zeroC : isContr (fst (HC 3)))
  (degree-two : (a : fst (HA 2)) → equivFun (fst eW₂) (source 2 a)
    ≡ fst D (equivFun (fst eA₂) a)) where

  private
    square₂ : (a : fst (HA 2)) → equivFun (fst eW₂) (fst s₂ a)
      ≡ fst D (equivFun (fst eA₂) a)
    square₂ a = cong (equivFun (fst eW₂)) (s₂-agrees a) ∙ degree-two a
    module Change₂ = ChangeKernel eA₂ eW₂ s₂ D square₂

  module ForSequence
    (vertices : (n : ℕ) → fst (DirProd (HB n) (HC n)) → fst (HP n))
    (L : SpanSequenceData HA HB HC HP source vertices) where
    private
      module L = SpanSequenceData L
      module Q = Canonical HA HB HC HP source vertices L s₂ s₁ s₂-agrees s₁-agrees
      module T = Q.Top zeroB zeroC
      module DK = DiagonalKernel (L.boundary 2) s₂ eA₂ eW₂ square₂
        T.kernel-equiv T.kernel-equiv-coordinate
      module R = DiagonalData DK.diagonal-data

    Marked : Type
    Marked = Σ[ e ∈ GroupEquiv (HP 3) ℤGroup ]
      ((t : ℤ) → equivFun (fst eA₂) (fst (L.boundary 2) (invEq (fst e) t)) ≡ fst diagonal t)

    abstract
      marked : Marked
      marked = R.integer-equiv , λ t →
        cong (λ b → equivFun (fst eA₂) (fst b (invEq (fst R.integer-equiv) t)))
          (sym DK.diagonal-boundary)
        ∙ R.diagonal-coordinate t

      H₂-zero : (p q r : ℤ)
        → ((a : fst (HA 1)) → equivFun (fst eW₁) (source 1 a)
            ≡ fst (Araw p q r) (equivFun (fst eA₁) a))
        → ((a : fst ℤ⁶) → fst (Araw p q r) a ≡ GroupStr.1g (snd (AbGroup→Group vertex₁))
            → a ≡ GroupStr.1g (snd (AbGroup→Group ℤ⁶)))
        → isContr (fst (HP 2))
      H₂-zero p q r degree-one kill = Q.H₂-zero
        (Change₂.onto-from-section (fst D-section) D-split)
        (Change₁.injective-from-kernel kill)
        where
        square₁ : (a : fst (HA 1)) → equivFun (fst eW₁) (fst s₁ a)
          ≡ fst (Araw p q r) (equivFun (fst eA₁) a)
        square₁ a = cong (equivFun (fst eW₁)) (s₁-agrees a) ∙ degree-one a
        module Change₁ = ChangeKernel eA₁ eW₁ s₁ (Araw p q r) square₁
