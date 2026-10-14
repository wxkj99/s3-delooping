{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ChainTools where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; isContrFin1 ; ¬Fin0)
open import Cubical.Data.Sigma using (Σ≡Prop)
import Cubical.Data.Empty as Empty
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.ChainComplex.Base using (ChainComplex)
open import Cubical.Algebra.ChainComplex.Homology using (homology)
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; CW-AugChainComplex)
import Cubical.CW.ChainComplex as CC
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)

-- All indices here are ordinary reduced homology degrees.  The augmented
-- chain complex places the k-cells in chain (suc k).
abstract
  chosen-skeleton : (X : CW₀) (s : hasCWskel (fst X)) (k : ℕ)
    → GroupEquiv (H̃ᶜʷ X k) (H̃ˢᵏᵉˡ (fst s) k)
  chosen-skeleton X s k = invEq (GroupPath _ _)
    (cong (λ w → H̃ᶜʷ (fst X , w) k) (PT.squash₁ (snd X) PT.∣ s ∣₁))

  chosen-zero : (X : CW₀) (s : hasCWskel (fst X)) (k : ℕ)
    → isContr (fst (H̃ˢᵏᵉˡ (fst s) k)) → Hzero X k
  chosen-zero X s k = isOfHLevelRespectEquiv 0
    (invEquiv (fst (chosen-skeleton X s k)))

  chosen-skeleton-path : (X : CW₀) (s : hasCWskel (fst X)) (k : ℕ)
    → chosen-skeleton X s k
     ≡ invEq (GroupPath (H̃ᶜʷ X k) (H̃ˢᵏᵉˡ (fst s) k))
         (cong (λ w → H̃ᶜʷ (fst X , w) k)
           (PT.squash₁ (snd X) PT.∣ s ∣₁))
  chosen-skeleton-path X s k = refl

zero-kernel-homology : (C : ChainComplex ℓ-zero) (k : ℕ)
  → ((x : fst (ChainComplex.chain C (suc k)))
    → fst (ChainComplex.bdry C k) x
        ≡ GroupStr.1g (snd (AbGroup→Group (ChainComplex.chain C k)))
    → x ≡ GroupStr.1g (snd (AbGroup→Group (ChainComplex.chain C (suc k)))))
  → isContr (fst (homology k C))
zero-kernel-homology C k kill = GroupStr.1g (snd (homology k C)) ,
  SQ.elimProp (λ _ → GroupStr.is-set (snd (homology k C)) _ _)
    (λ z → cong SQ.[_] (Σ≡Prop
      (λ _ → GroupStr.is-set (snd (AbGroup→Group (ChainComplex.chain C k))) _ _)
      (sym (kill (fst z) (snd z)))))

no-cells-homology : (C : CWskel ℓ-zero) (k : ℕ)
  → C .snd .fst k ≡ 0 → isContr (fst (H̃ˢᵏᵉˡ C k))
no-cells-homology C k p = zero-kernel-homology (CW-AugChainComplex C) k
  λ x _ → subst (λ r → (x : Fin r → ℤ) → x ≡ (λ _ → pos 0))
    (sym p) (λ x → funExt λ y → Empty.rec (¬Fin0 y)) x

one-vertex-homology : (C : CWskel ℓ-zero)
  → C .snd .fst 0 ≡ 1 → isContr (fst (H̃ˢᵏᵉˡ C 0))
one-vertex-homology C p = zero-kernel-homology (CW-AugChainComplex C) 0
  λ x ker → subst (λ r → (x : Fin r → ℤ)
    → Z.sumFinℤ x ≡ pos 0 → x ≡ (λ _ → pos 0)) (sym p)
      (λ x q → funExt λ y → cong x (sym (snd isContrFin1 y)) ∙ q) x
      (sym (funExt⁻ (funExt⁻ (cong fst (CC.augmentation.ϵ-alt C)) x) fzero)
        ∙ funExt⁻ ker fzero)
