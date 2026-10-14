{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.Seam where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (rUnit; ∙∙lCancel)
open import Cubical.Foundations.Path using (Square≃doubleComp)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Homotopy.Group.Base using (πGr; πHom)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.SetTruncation as ST

Π : ∀ {ℓ} (Y : Type ℓ) → Y → Group ℓ
Π Y y = πGr 0 (Y , y)

abstract
  -- πHom includes the (trivial here) pointing conjugation.
  πHom-loop : ∀ {ℓ ℓ'} {Y : Type ℓ} {Z : Type ℓ'}
    (f : Y → Z) (a : Y) (l : a ≡ a)
    → fst (πHom 0 (f , refl)) ST.∣ l ∣₂ ≡ ST.∣ cong f l ∣₂
  πHom-loop f a l = cong ST.∣_∣₂ (sym (rUnit (cong f l)))

module PushoutKernel {ℓA ℓB ℓC}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  (q : A → B) (p : A → C) (a : A) where

  private
    X : Type (ℓ-max ℓA (ℓ-max ℓB ℓC))
    X = Pushout q p
    left : B → X
    left = inl
    right : C → X
    right = inr
    seam : (v : A) → left (q v) ≡ right (p v)
    seam = push
    x : X
    x = right (p a)
    transportLoop : fst (Π B (q a)) → fst (Π X x)
    transportLoop = ST.map (λ l → sym (seam a) ∙∙ cong left l ∙∙ seam a)

  abstract
    seam-naturality : (l : a ≡ a)
      → sym (seam a) ∙∙ cong (left ∘ q) l ∙∙ seam a
        ≡ cong (right ∘ p) l
    seam-naturality l = equivFun (Square≃doubleComp _ _ (seam a) (seam a))
      (λ i j → seam (l j) i)

    seam-π : (u : fst (Π A a))
      → transportLoop (fst (πHom 0 (q , refl)) u)
        ≡ fst (πHom 0 (right , refl)) (fst (πHom 0 (p , refl)) u)
    seam-π = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) λ l →
      cong transportLoop (πHom-loop q a l)
      ∙ cong ST.∣_∣₂ (seam-naturality l)
      ∙ sym (cong (fst (πHom 0 (right , refl))) (πHom-loop p a l)
        ∙ πHom-loop right (p a) (cong p l))

    pushout-kills-kernel : (u : fst (Π A a))
      → fst (πHom 0 (q , refl)) u ≡ GroupStr.1g (snd (Π B (q a)))
      → fst (πHom 0 (right , refl)) (fst (πHom 0 (p , refl)) u)
        ≡ GroupStr.1g (snd (Π X x))
    pushout-kills-kernel u eq = sym (seam-π u)
      ∙ cong transportLoop eq ∙ cong ST.∣_∣₂ (∙∙lCancel (seam a))

open PushoutKernel public using (pushout-kills-kernel)
