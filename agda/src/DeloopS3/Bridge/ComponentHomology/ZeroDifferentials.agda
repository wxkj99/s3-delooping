{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ZeroDifferentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma using (Σ≡Prop)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.ChainComplex.Base using (ChainComplex)
open import Cubical.Algebra.ChainComplex.Homology using (homology)

-- Pure algebra applied below to the ACTUAL cellular chain complex.
module _ (C : ChainComplex ℓ-zero) (k : ℕ)
  (out-zero : ChainComplex.bdry C k ≡ trivGroupHom)
  (in-zero : ChainComplex.bdry C (suc k) ≡ trivGroupHom) where
  private
    G : Group₀
    G = AbGroup→Group (ChainComplex.chain C (suc k))

    lowerGroup : Group₀
    lowerGroup = AbGroup→Group (ChainComplex.chain C k)

    decode : fst (homology k C) → fst G
    decode = SQ.rec (GroupStr.is-set (snd G)) fst
      (λ x y → PT.rec (GroupStr.is-set (snd G) _ _)
        (λ (t , p) → GroupTheory.invUniqueL G
          (sym (cong fst p) ∙ funExt⁻ (cong fst in-zero) t)
          ∙ GroupTheory.invInv G (fst y)))

    encode : fst G → fst (homology k C)
    encode x = SQ.[ x , funExt⁻ (cong fst out-zero) x ]

  zero-differentials-iso : GroupIso (homology k C) G
  Iso.fun (fst zero-differentials-iso) = decode
  Iso.inv (fst zero-differentials-iso) = encode
  Iso.sec (fst zero-differentials-iso) x = refl
  Iso.ret (fst zero-differentials-iso) = SQ.elimProp
    (λ _ → GroupStr.is-set (snd (homology k C)) _ _)
    (λ (x , p) → cong SQ.[_] (Σ≡Prop (λ _ → GroupStr.is-set (snd lowerGroup) _ _) refl))
  snd zero-differentials-iso = makeIsGroupHom
    (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd G) _ _) (λ _ _ → refl))
