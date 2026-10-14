{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.OuterAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (zero ; suc ; snotz)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_ ; ℤ/2-elim ; ℤ/2-rec)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.IntMod using (ℤAbGroup/_)
import Cubical.HITs.PropositionalTruncation as PT

C₂ C₄ : Group₀
C₂ = ℤGroup/ 2
C₄ = ℤGroup/ 4
private
  module Two = GroupStr (snd C₂)
  module Four = GroupStr (snd C₄)

zero₂ one₂ : fst C₂
zero₂ = fzero
one₂ = fsuc fzero

scale₂ : fst C₂ → fst C₂ → fst C₂
scale₂ e = ℤ/2-rec zero₂ e

abstract
  scale₂-hom : (e x y : fst C₂) → scale₂ e (x Two.· y) ≡ scale₂ e x Two.· scale₂ e y
  scale₂-hom = ℤ/2-elim
    (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
    (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))

  cancel₂ : (x y : fst C₂) → (x Two.· y) Two.· y ≡ x
  cancel₂ = ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl)

-- The chosen J generator may have either target coordinate e.
-- Both matrices are invertible without a p(J)=0 marking.
o-map : fst C₂ → GroupHom (DirProd C₂ C₂) (DirProd C₂ C₂)
fst (o-map e) (r , j) = j , r Two.· scale₂ e j
snd (o-map e) = makeIsGroupHom λ (r , j) (s , k) → ΣPathP (refl ,
  cong ((r Two.· s) Two.·_) (scale₂-hom e j k)
  ∙ AbGroupTheory.comm-4 (ℤAbGroup/ 2) r s (scale₂ e j) (scale₂ e k))

o-isomorphism : (e : fst C₂) → GroupIso (DirProd C₂ C₂) (DirProd C₂ C₂)
Iso.fun (fst (o-isomorphism e)) = fst (o-map e)
Iso.inv (fst (o-isomorphism e)) (t , x) = x Two.· scale₂ e t , t
Iso.sec (fst (o-isomorphism e)) (t , x) = ΣPathP (refl , cancel₂ x (scale₂ e t))
Iso.ret (fst (o-isomorphism e)) (r , j) = ΣPathP (cancel₂ r (scale₂ e j) , refl)
snd (o-isomorphism e) = snd (o-map e)

abstract
  o-r-image : (e : fst C₂) → fst (o-map e) (one₂ , zero₂) ≡ (zero₂ , one₂)
  o-r-image e = refl
  o-j-image : (e : fst C₂) → fst (o-map e) (zero₂ , one₂) ≡ (one₂ , e)
  o-j-image e = ΣPathP (refl , Two.·IdL e)

four-elim : ∀ {ℓ} {P : Fin 4 → Type ℓ}
  → P fzero → P (fsuc fzero) → P (fsuc (fsuc fzero)) → P (fsuc (fsuc (fsuc fzero)))
  → (x : Fin 4) → P x
four-elim a b c d (zero , p) = a
four-elim a b c d (suc zero , p) = b
four-elim a b c d (suc (suc zero) , p) = c
four-elim a b c d (suc (suc (suc zero)) , p) = d
four-elim a b c d (suc (suc (suc (suc n))) , p) = Empty.rec p

mod₂ : fst C₄ → fst C₂
mod₂ = four-elim zero₂ one₂ zero₂ one₂

i-map : GroupHom C₄ C₂
fst i-map = mod₂
snd i-map = makeIsGroupHom (four-elim
  (four-elim refl refl refl refl)
  (four-elim refl refl refl refl)
  (four-elim refl refl refl refl)
  (four-elim refl refl refl refl))

abstract
  i-onto : isSurjective i-map
  i-onto = ℤ/2-elim PT.∣ fzero , refl ∣₁ PT.∣ fsuc fzero , refl ∣₁

private
  double : fst C₂ → fst (kerGroup i-map)
  double = ℤ/2-elim (fzero , refl) (fsuc (fsuc fzero) , refl)

  half : (x : fst C₄) → mod₂ x ≡ zero₂ → fst C₂
  half = four-elim (λ _ → zero₂) (λ p → Empty.rec (snotz (cong fst p)))
    (λ _ → one₂) (λ p → Empty.rec (snotz (cong fst p)))

  half-double : (a : fst C₂) → half (fst (double a)) (snd (double a)) ≡ a
  half-double = ℤ/2-elim refl refl

  double-half : (x : fst C₄) (p : mod₂ x ≡ zero₂) → double (half x p) ≡ (x , p)
  double-half = four-elim
    (λ p → kerGroup≡ i-map refl)
    (λ p → Empty.rec (snotz (cong fst p)))
    (λ p → kerGroup≡ i-map refl)
    (λ p → Empty.rec (snotz (cong fst p)))

  doubling-iso : GroupIso C₂ (kerGroup i-map)
  Iso.fun (fst doubling-iso) = double
  Iso.inv (fst doubling-iso) (x , p) = half x p
  Iso.sec (fst doubling-iso) (x , p) = double-half x p
  Iso.ret (fst doubling-iso) = half-double
  snd doubling-iso = makeIsGroupHom (ℤ/2-elim
    (ℤ/2-elim (kerGroup≡ i-map refl) (kerGroup≡ i-map refl))
    (ℤ/2-elim (kerGroup≡ i-map refl) (kerGroup≡ i-map refl)))

i-kernel : GroupEquiv (kerGroup i-map) C₂
i-kernel = GroupIso→GroupEquiv (invGroupIso doubling-iso)

i-kernel-generator : invEq (fst i-kernel) one₂ ≡ (fsuc (fsuc fzero) , refl)
i-kernel-generator = refl
