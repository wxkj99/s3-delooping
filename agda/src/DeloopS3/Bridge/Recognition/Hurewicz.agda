{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.Hurewicz where

-- Hurewicz connectivity steps and merely existing sphere representatives.
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.Recognition.Connectivity
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Algebra.AbGroup.Base using (Group→AbGroup)
open import Cubical.Algebra.Group.Abelianization.Properties using
  (AbelianizationIdempotent)
open import Cubical.Homotopy.Group.Base using (π'Gr ; π'-comm ; π'Gr≅πGr)
open import Cubical.Homotopy.Connected
open import Cubical.CW.HurewiczTheorem using (HurewiczTheorem ; HurewiczHomAb ; HurewiczMap ; HurewiczMapUntrunc)
import Cubical.HITs.Truncation as TR
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Sn.Base using (S₊∙)

open import DeloopS3.Bridge.Recognition.HurewiczBase public using (hurewicz-equiv)

hurewicz-raise : (X : CW₀) (n : ℕ)
  → isConnected (3 + n) (fst X)
  → Hzero X (2 + n)
  → isConnected (4 + n) (fst X)
hurewicz-raise X n conn zeroH = TR.rec {A = fst X} {n = 3 + n}
  (isProp→isOfHLevelSuc (2 + n) isPropIsContr) at-point (fst conn)
  where
  at-point : (x : fst X) → isConnected (4 + n) (fst X)
  at-point x = raise-from-π (2 + n) (fst X , x) conn
    (isOfHLevelRetractFromIso 0
      (invIso (fst (π'Gr≅πGr (suc n) (fst X , x))))
      (isOfHLevelRetractFromIso 0
        (equivToIso (hurewicz-equiv X n conn x)) zeroH))

-- Choose a sphere representative only inside propositional truncation.
hurewicz-representative : (X : CW₀) (n : ℕ)
  (conn : isConnected (3 + n) (fst X)) (x : fst X)
  (h : fst (H̃ᶜʷ X (2 + n)))
  → PT.∥ Σ[ s ∈ (S₊∙ (2 + n) →∙ (fst X , x)) ]
      (HurewiczMapUntrunc {n = suc n} X x s ≡ h) ∥₁
hurewicz-representative X n conn x h = choose (invEq e h) (secEq e h)
  where
  e = hurewicz-equiv X n conn x
  choose : (a : fst (π'Gr (suc n) (fst X , x))) → fst e a ≡ h
    → PT.∥ Σ[ s ∈ (S₊∙ (2 + n) →∙ (fst X , x)) ]
        (HurewiczMapUntrunc {n = suc n} X x s ≡ h) ∥₁
  choose = ST.elim (λ _ → isProp→isSet (isPropΠ λ _ → PT.squash₁))
    (λ s p → PT.∣ s , p ∣₁)

-- An equality of Hurewicz classes gives only a MERELY existing pointed
-- homotopy.  Forgetting the pointing afterwards is harmless.
hurewicz-equality→merely-homotopy : (X : CW₀) (n : ℕ)
  (conn : isConnected (3 + n) (fst X)) (x : fst X)
  (s t : S₊∙ (2 + n) →∙ (fst X , x))
  → HurewiczMapUntrunc {n = suc n} X x s ≡ HurewiczMapUntrunc {n = suc n} X x t
  → PT.∥ s ≡ t ∥₁
hurewicz-equality→merely-homotopy X n conn x s t p =
  Iso.fun ST.PathIdTrunc₀Iso
    (sym (retEq e ST.∣ s ∣₂) ∙ cong (invEq e) p ∙ retEq e ST.∣ t ∣₂)
  where
  e = hurewicz-equiv X n conn x

-- These are exactly HurewiczTheorem 3 and HurewiczTheorem 4,
-- after the abelianization adapter and bounded Whitehead step above.
two-hurewicz-steps : (C : CW₀)
  → isConnected 5 (fst C) → Hzero C 4 → Hzero C 5
  → isConnected 7 (fst C)
two-hurewicz-steps C conn h4 h5 =
  hurewicz-raise C 3 (hurewicz-raise C 2 conn h4) h5
