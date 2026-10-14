{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- A change of pointed circle frame changes integer coordinates only by sign.
-- This frame-change result does not fix the stock sphere-chart orientation.
module DeloopS3.Seifert.TwistedBundle.FrameSign where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Int
  using (ℤ; pos; negsuc; _+_; _·_; -_; -Involutive; ·Assoc)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (makeIsGroupHom; GroupEquiv→GroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction using (ℤEquiv1; characGroupHomℤ)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-comp)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (ΩEM₁Iso)
open import Cubical.Homotopy.Loopspace using (Ω→; Ω≃∙; Ω→pres∙)
open import DeloopS3.Move.CancelMinimal using (C; 0C)

Aut-ℤ-sign : (φ : GroupEquiv ℤGroup ℤGroup)
  → (φ .fst .fst (pos 1) ≡ pos 1) ⊎ (φ .fst .fst (pos 1) ≡ negsuc 0)
Aut-ℤ-sign = ℤEquiv1

-- Match Connecting's convention: false is positive, true is negative.
signℤ : Bool → ℤ
signℤ false = pos 1
signℤ true = negsuc 0

-- A single sign works simultaneously for every integer, not just pointwise.
Aut-ℤ-sign-all : (φ : GroupEquiv ℤGroup ℤGroup)
  → Σ[ s ∈ Bool ] ((n : ℤ) → φ .fst .fst n ≡ signℤ s · n)
Aut-ℤ-sign-all φ with Aut-ℤ-sign φ
... | inl p = false , λ n →
  cong (λ h → h .fst n) (characGroupHomℤ (GroupEquiv→GroupHom φ))
  ∙ cong (_· n) p
... | inr p = true , λ n →
  cong (λ h → h .fst n) (characGroupHomℤ (GroupEquiv→GroupHom φ))
  ∙ cong (_· n) p

encC : (0C ≡ 0C) → ℤ
encC = Iso.fun (ΩEM₁Iso ℤGroup)

encC-emloop : (n : ℤ) → encC (emloop n) ≡ n
encC-emloop = Iso.sec (ΩEM₁Iso ℤGroup)

emloop-encC : (p : 0C ≡ 0C) → emloop (encC p) ≡ p
emloop-encC = Iso.ret (ΩEM₁Iso ℤGroup)

encC-comp : (p q : 0C ≡ 0C) → encC (p ∙ q) ≡ encC p + encC q
encC-comp p q =
  cong encC (cong₂ _∙_ (sym (emloop-encC p)) (sym (emloop-encC q))
    ∙ sym (emloop-comp ℤGroup (encC p) (encC q)))
  ∙ encC-emloop (encC p + encC q)

-- Conjugate the actual based loop map by ΩEM₁Iso. In particular, the
-- basepoint path of e is retained in Ω→; no strict-pointedness is assumed.
C-autoℤ : (e : (C , 0C) ≃∙ (C , 0C)) → GroupEquiv ℤGroup ℤGroup
C-autoℤ e .fst = isoToEquiv
  (compIso (invIso (ΩEM₁Iso ℤGroup))
    (compIso (equivToIso (Ω≃∙ e .fst)) (ΩEM₁Iso ℤGroup)))
C-autoℤ e .snd = makeIsGroupHom λ n m →
  cong (encC ∘ Ω→ (e .fst .fst , e .snd) .fst) (emloop-comp ℤGroup n m)
  ∙ cong encC (Ω→pres∙ (e .fst .fst , e .snd) (emloop n) (emloop m))
  ∙ encC-comp (Ω→ (e .fst .fst , e .snd) .fst (emloop n))
              (Ω→ (e .fst .fst , e .snd) .fst (emloop m))

pointed-C-auto-sign : (e : (C , 0C) ≃∙ (C , 0C))
  → Σ[ s ∈ Bool ] ((n : ℤ)
      → encC (Ω→ (e .fst .fst , e .snd) .fst (emloop n)) ≡ signℤ s · n)
pointed-C-auto-sign e = Aut-ℤ-sign-all (C-autoℤ e)

-- The form useful for a connecting map: the input can be any based loop,
-- rather than one already written as an integer generator power.
pointed-C-frame-change : (e : (C , 0C) ≃∙ (C , 0C))
  → Σ[ s ∈ Bool ] ((p : 0C ≡ 0C)
      → encC (Ω→ (e .fst .fst , e .snd) .fst p) ≡ signℤ s · encC p)
pointed-C-frame-change e = s , λ p →
  cong (encC ∘ Ω→ (e .fst .fst , e .snd) .fst) (sym (emloop-encC p))
  ∙ computation (encC p)
  where
  s = pointed-C-auto-sign e .fst
  computation = pointed-C-auto-sign e .snd

-- Absorb the frame sign into the Euler coefficient, preserving nonvanishing.
sign-absorb : (s : Bool) (k n : ℤ)
  → signℤ s · (k · n) ≡ (signℤ s · k) · n
sign-absorb s k n = ·Assoc (signℤ s) k n

sign-involutive : (s : Bool) (n : ℤ) → signℤ s · (signℤ s · n) ≡ n
sign-involutive false n = refl
sign-involutive true n = -Involutive n

sign-zero : (s : Bool) → signℤ s · pos 0 ≡ pos 0
sign-zero false = refl
sign-zero true = refl

sign-nonzero : (s : Bool) (n : ℤ)
  → ¬ (n ≡ pos 0) → ¬ (signℤ s · n ≡ pos 0)
sign-nonzero s n nz p = nz
  (sym (sign-involutive s n) ∙ cong (signℤ s ·_) p ∙ sign-zero s)

sign-nonzero-reflect : (s : Bool) (n : ℤ)
  → ¬ (signℤ s · n ≡ pos 0) → ¬ (n ≡ pos 0)
sign-nonzero-reflect s n nz p = nz (cong (signℤ s ·_) p ∙ sign-zero s)
