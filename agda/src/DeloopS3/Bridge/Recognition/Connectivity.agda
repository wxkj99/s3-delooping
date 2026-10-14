{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Connectivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace using (Ω)
open import Cubical.Homotopy.Group.Base using (π ; Iso-πΩ-π)
import Cubical.HITs.Truncation as TR

-- Bounded Whitehead using the next homotopy group; lower groups vanish
-- by connectivity. Induction takes loops, not untruncated Whitehead.
raise-from-π : (n : ℕ) (A : Pointed ℓ-zero)
  → isConnected (suc n) (fst A)
  → isContr (π n A)
  → isConnected (suc (suc n)) (fst A)
raise-from-π zero A connA πzero =
  isOfHLevelRetractFromIso 0 (invIso TR.setTruncTrunc2Iso) πzero
raise-from-π (suc n) A connA πzero =
  TR.∣ snd A ∣ , TR.elim
    (λ _ → isOfHLevelPath (suc (suc (suc n)))
      (TR.isOfHLevelTrunc (suc (suc (suc n)))) _ _)
    (λ b → Iso.inv (TR.PathIdTruncIso (suc (suc n))) (paths b .fst))
  where
  loops : isConnected (suc (suc n)) (snd A ≡ snd A)
  loops = raise-from-π n (Ω A)
    (isConnectedPath (suc n) connA (snd A) (snd A))
    (isOfHLevelRetractFromIso 0 (Iso-πΩ-π n) πzero)

  paths : (b : fst A) → isConnected (suc (suc n)) (snd A ≡ b)
  paths b = TR.rec isPropIsContr
    (λ p → subst (λ b → isConnected (suc (suc n)) (snd A ≡ b)) p loops)
    (isConnectedPath 1 (isConnectedSubtr' n 2 connA) (snd A) b .fst)
