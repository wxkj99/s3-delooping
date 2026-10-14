{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.SeifertChains.Block where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CellularPushout.Algebra using
  (pairHom ; fstHom ; sndHom)
import DeloopS3.Bridge.DMCExactness.Quotient as Q
open import DeloopS3.Bridge.ComponentHomology.ChainTools using (zero-kernel-homology)
open import Cubical.Data.Unit using (isContrUnit*)

open ChainComplex
open IsGroupHom

-- The zero-differential-piece specialization of the normalized DMC:
-- remove only zero summands, NOT overlap prisms.  E is its ONE augmentation.
-- L = rose edges, R = boundary components, V = overlap one-cells.
module Blocks (E L R V : AbGroup ℓ-zero)
  (S : AbGroupHom R E)
  (D : AbGroupHom R L)
  (A : AbGroupHom V (dirProdAb L (dirProdAb E R))) where

  vertex₁ : AbGroup ℓ-zero
  vertex₁ = dirProdAb L (dirProdAb E R)

  groups : ℕ → AbGroup ℓ-zero
  groups zero = E
  groups 1 = dirProdAb E R
  groups 2 = dirProdAb vertex₁ R
  groups 3 = dirProdAb L V
  groups 4 = R
  groups (suc (suc (suc (suc (suc n))))) = UnitAbGroup

  differential : (n : ℕ) → AbGroupHom (groups (suc n)) (groups n)
  differential zero = addGroupHom (dirProdAb E R) E
    (fstHom E R) (compGroupHom (sndHom E R) S)
  differential 1 = compGroupHom (sndHom vertex₁ R)
    (pairHom S (negGroupHom R R idGroupHom))
  differential 2 = pairHom (compGroupHom (sndHom L V) A) trivGroupHom
  differential 3 = pairHom D trivGroupHom
  differential (suc (suc (suc (suc n)))) = trivGroupHom

  abstract
    square : (n : ℕ) → compGroupHom (differential (suc n)) (differential n)
      ≡ trivGroupHom
    square zero = GroupHom≡ (funExt λ x →
      cong (AbGroupStr._+_ (snd E) (fst S (snd x))) (presinv (snd S) (snd x))
      ∙ AbGroupStr.+InvR (snd E) (fst S (snd x)))
    square 1 = GroupHom≡ (funExt λ x → ΣPathP
      (pres1 (snd S) , GroupTheory.inv1g (AbGroup→Group R)))
    square 2 = GroupHom≡ (funExt λ x → ΣPathP (pres1 (snd A) , refl))
    square 3 = GroupHom≡ (funExt λ x → ΣPathP (pres1 (snd D) , refl))
    square (suc (suc (suc (suc n)))) = GroupHom≡ (funExt λ _ → refl)

  K : ChainComplex ℓ-zero
  chain K = groups
  bdry K = differential
  bdry²=0 K = square

  abstract
    above-three-zero : (n : ℕ)
      → isContr (fst (homology (suc (suc (suc (suc n)))) K))
    above-three-zero n = zero-kernel-homology K (suc (suc (suc (suc n))))
      (λ x _ → sym (snd isContrUnit* x))

    top-cycles : GroupEquiv (ker∂n 3 K) (kerGroup D)
    top-cycles = GroupIso→GroupEquiv (topIso , makeIsGroupHom λ _ _ → kerGroup≡ D refl)
      where
      topIso : Iso (fst (ker∂n 3 K)) (fst (kerGroup D))
      Iso.fun topIso (x , p) = x , cong fst p
      Iso.inv topIso (x , p) = x , ΣPathP (p , refl)
      Iso.sec topIso _ = kerGroup≡ D refl
      Iso.ret topIso _ = kerGroup≡ (differential 3) refl

    top-cycles-coordinate : (z : fst (ker∂n 3 K))
      → fst (equivFun (fst top-cycles) z) ≡ fst z
    top-cycles-coordinate _ = refl

    top-cycles-inverse : (z : fst (kerGroup D))
      → fst (invEq (fst top-cycles) z) ≡ fst z
    top-cycles-inverse _ = refl

    H₂-zero : (section : fst L → fst R)
      → ((x : fst L) → fst D (section x) ≡ x)
      → ((v : fst V) → fst A v ≡ AbGroupStr.0g (snd vertex₁)
          → v ≡ AbGroupStr.0g (snd V))
      → isContr (fst (homology 2 K))
    H₂-zero section split kill = GroupStr.1g (snd (homology 2 K)) ,
      SQ.elimProp (λ _ → GroupStr.is-set (snd (homology 2 K)) _ _)
        λ z → sym (H.boundary→zero z (section (fst (fst z)))
          (ΣPathP (split (fst (fst z)) , sym (kill (snd (fst z)) (cong fst (snd z))))))
      where module H = Q.Homology K 2

-- Quotienting top cycles by a zero incoming differential changes nothing.
-- Keep this proof over an abstract complex to avoid expanding concrete kernels.
module NoIncoming (C : ChainComplex ℓ-zero) (n : ℕ)
  (incoming : (x : fst (chain C (suc (suc n))))
    → fst (bdry C (suc n)) x ≡ AbGroupStr.0g (snd (chain C (suc n)))) where
  private
    G : Group ℓ-zero
    G = ker∂n n C
    module G = GroupStr (snd G)
    module GT = GroupTheory G

    abstract
      relation : (x y : fst G)
        → _~_ G (fst (img∂+1⊂ker∂n n C)) (snd (img∂+1⊂ker∂n n C)) x y
        → x ≡ y
      relation x y = PT.rec (G.is-set x y) λ v →
        GT.invUniqueL (sym (snd v) ∙ kerGroup≡ (bdry C n) (incoming (fst v)))
          ∙ GT.invInv y

  cycle-to-H : GroupEquiv G (homology n C)
  cycle-to-H = GroupIso→GroupEquiv (trivialRelIso (img∂+1⊂ker∂n n C) relation)

  H-to-cycle : GroupEquiv (homology n C) G
  H-to-cycle = invGroupEquiv cycle-to-H

  abstract
    H-to-cycle-inverse : (z : fst G) → invEq (fst H-to-cycle) z ≡ SQ.[ z ]
    H-to-cycle-inverse _ = refl

    H-to-cycle-class : (z : fst G) → equivFun (fst H-to-cycle) SQ.[ z ] ≡ z
    H-to-cycle-class _ = refl
