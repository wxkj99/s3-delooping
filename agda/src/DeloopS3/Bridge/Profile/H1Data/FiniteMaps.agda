{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.FiniteMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (snotz)
open import Cubical.Data.Fin using (fzero ; fsuc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.IntMod using (ℤ/2-elim ; ℤ/2-rec)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Profile.H1Data.OuterAlgebra

V₄ : Group₀
V₄ = DirProd C₂ C₂
private
  module T = GroupStr (snd C₂)
  module V = GroupStr (snd V₄)
  z a b d : fst V₄
  z = zero₂ , zero₂
  a = zero₂ , one₂
  b = one₂ , zero₂
  d = one₂ , one₂

pair₂-elim : ∀ {ℓ} {P : fst V₄ → Type ℓ}
  → P z → P a → P b → P d → (x : fst V₄) → P x
pair₂-elim {P = P} pz pa pb pd (x , y) =
  ℤ/2-elim {A = λ x → (y : fst C₂) → P (x , y)}
    (ℤ/2-elim pz pa) (ℤ/2-elim pb pd) x y

private
  bit-vector : fst C₂ → fst V₄ → fst V₄
  bit-vector t r = ℤ/2-rec z r t
  basis : fst V₄ → fst V₄ → fst V₄ → fst V₄
  basis r s (x , y) = bit-vector x r V.· bit-vector y s
  adjugate : fst V₄ → fst V₄ → fst V₄ → fst V₄
  adjugate (r , t) (s , u) (x , y) =
    scale₂ u x T.· scale₂ s y , scale₂ t x T.· scale₂ r y

  -- Only the six independent ordered pairs survive. This is a bounded
  -- constructive calculation in C₂², not a general cardinality axiom.
  basis-laws : (r s : fst V₄) → (r ≡ z → ⊥) → (s ≡ z → ⊥) → (r ≡ s → ⊥)
    → (x : fst V₄) → (basis r s (adjugate r s x) ≡ x) × (adjugate r s (basis r s x) ≡ x)
  basis-laws = pair₂-elim
    (λ s nr ns nd x → Empty.rec (nr refl))
    (pair₂-elim
      (λ nr ns nd x → Empty.rec (ns refl))
      (λ nr ns nd x → Empty.rec (nd refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl)))
    (pair₂-elim
      (λ nr ns nd x → Empty.rec (ns refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl))
      (λ nr ns nd x → Empty.rec (nd refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl)))
    (pair₂-elim
      (λ nr ns nd x → Empty.rec (ns refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl))
      (λ nr ns nd → pair₂-elim (refl , refl) (refl , refl) (refl , refl) (refl , refl))
      (λ nr ns nd x → Empty.rec (nd refl)))

  onto-preimages-equiv : (f : GroupHom V₄ V₄) (r s : fst V₄)
    → fst f r ≡ b → fst f s ≡ a → isEquiv (fst f)
  onto-preimages-equiv f r s pr ps = isoToIsEquiv (iso (fst f) (basis r s) right-inverse left-inverse)
    where
    nr : r ≡ z → ⊥
    nr e = snotz (cong (fst ∘ fst) (sym pr ∙ cong (fst f) e ∙ IsGroupHom.pres1 (snd f)))
    ns : s ≡ z → ⊥
    ns e = snotz (cong (fst ∘ snd) (sym ps ∙ cong (fst f) e ∙ IsGroupHom.pres1 (snd f)))
    nd : r ≡ s → ⊥
    nd e = snotz (cong (fst ∘ fst) (sym pr ∙ cong (fst f) e ∙ ps))
    eBasis : fst V₄ ≃ fst V₄
    eBasis = isoToEquiv (iso (basis r s) (adjugate r s)
      (λ x → fst (basis-laws r s nr ns nd x)) (λ x → snd (basis-laws r s nr ns nd x)))
    right-inverse : (x : fst V₄) → fst f (basis r s x) ≡ x
    right-inverse = pair₂-elim (IsGroupHom.pres1 (snd f))
      (cong (fst f) (V.·IdL s) ∙ ps)
      (cong (fst f) (V.·IdR r) ∙ pr)
      (IsGroupHom.pres· (snd f) r s ∙ cong₂ V._·_ pr ps)
    left-inverse : (x : fst V₄) → basis r s (fst f x) ≡ x
    left-inverse x = cong (basis r s ∘ fst f) (sym (secEq eBasis x))
      ∙ cong (basis r s) (right-inverse (invEq eBasis x)) ∙ secEq eBasis x

abstract
  V₄-onto-isEquiv : (f : GroupHom V₄ V₄) → isSurjective f → isEquiv (fst f)
  V₄-onto-isEquiv f onto = PT.rec (isPropIsEquiv (fst f))
    (λ { (r , pr) → PT.rec (isPropIsEquiv (fst f))
      (λ { (s , ps) → onto-preimages-equiv f r s pr ps }) (onto a) }) (onto b)

private
  one₄ : fst C₄
  one₄ = fsuc fzero
  two₄ : fst C₄
  two₄ = fsuc (fsuc fzero)

  one-zero→zero : (f : GroupHom C₄ C₂) → fst f one₄ ≡ zero₂ → (x : fst C₄) → fst f x ≡ zero₂
  one-zero→zero f p = four-elim (IsGroupHom.pres1 (snd f)) p p₂
    (IsGroupHom.pres· (snd f) two₄ one₄ ∙ cong₂ T._·_ p₂ p)
    where
    p₂ : fst f two₄ ≡ zero₂
    p₂ = IsGroupHom.pres· (snd f) one₄ one₄ ∙ cong₂ T._·_ p p

  not-zero→one : (x : fst C₂) → (x ≡ zero₂ → ⊥) → x ≡ one₂
  not-zero→one = ℤ/2-elim (λ n → Empty.rec (n refl)) (λ _ → refl)

abstract
  C₄-onto-is-mod₂ : (f : GroupHom C₄ C₂) → isSurjective f → (x : fst C₄) → fst f x ≡ mod₂ x
  C₄-onto-is-mod₂ f onto = four-elim (IsGroupHom.pres1 (snd f)) p p₂
    (IsGroupHom.pres· (snd f) two₄ one₄ ∙ cong₂ T._·_ p₂ p)
    where
    nonzero : fst f one₄ ≡ zero₂ → ⊥
    nonzero e = PT.rec Empty.isProp⊥ (λ { (x , px) →
      snotz (cong fst (sym px ∙ one-zero→zero f e x)) }) (onto one₂)
    p : fst f one₄ ≡ one₂
    p = not-zero→one (fst f one₄) nonzero
    p₂ : fst f two₄ ≡ zero₂
    p₂ = IsGroupHom.pres· (snd f) one₄ one₄ ∙ cong₂ T._·_ p p

  C₄-onto-kernel : (f : GroupHom C₄ C₂) → isSurjective f → GroupEquiv (kerGroup f) C₂
  C₄-onto-kernel f onto = subst (λ g → GroupEquiv (kerGroup g) C₂)
    (sym (Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt (C₄-onto-is-mod₂ f onto)))) i-kernel
