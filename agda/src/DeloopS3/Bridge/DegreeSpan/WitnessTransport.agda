{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.WitnessTransport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq ; secEq)
open import Cubical.Foundations.Transport using (substCommSlice)
open import Cubical.Foundations.Univalence using (uaβ)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Algebra.Group using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.CW.Base using (hasCWskel ; isCW)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ ; H̃ᶜʷ→ ; H̃ˢᵏᵉˡ→)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀)
import Cubical.HITs.PropositionalTruncation as PT

witness-comparison : (X : CW₀) (s : hasCWskel (fst X)) (k : ℕ)
  → GroupEquiv (H̃ᶜʷ X k) (H̃ˢᵏᵉˡ (fst s) k)
witness-comparison X s k =
  invEq (GroupPath (H̃ᶜʷ X k) (H̃ˢᵏᵉˡ (fst s) k))
    (cong (λ w → H̃ᶜʷ (fst X , w) k)
      (PT.squash₁ (snd X) PT.∣ s ∣₁))

private
  abstract
    group-path-action : (G H : Group₀) (p : G ≡ H) (x : fst G)
      → fst (fst (invEq (GroupPath G H) p)) x
        ≡ transport (cong fst p) x
    group-path-action G H p x =
      sym (uaβ (fst e) x)
      ∙ cong (λ q → transport (cong fst q) x)
          (secEq (GroupPath G H) p)
      where
      e : GroupEquiv G H
      e = invEq (GroupPath G H) p

abstract
  witness-comparison-action : (X : CW₀) (s : hasCWskel (fst X))
    (k : ℕ) (x : fst (H̃ᶜʷ X k))
    → fst (fst (witness-comparison X s k)) x
      ≡ transport
          (λ i → fst (H̃ᶜʷ (fst X , PT.squash₁ (snd X) PT.∣ s ∣₁ i) k)) x
  witness-comparison-action X s k x =
    group-path-action (H̃ᶜʷ X k) (H̃ˢᵏᵉˡ (fst s) k)
      (cong (λ w → H̃ᶜʷ (fst X , w) k)
        (PT.squash₁ (snd X) PT.∣ s ∣₁)) x

  witness-comparison-natural : (X Y : CW₀)
    (sX : hasCWskel (fst X)) (sY : hasCWskel (fst Y))
    (k : ℕ) (f : fst X → fst Y) (x : fst (H̃ᶜʷ X k))
    → fst (fst (witness-comparison Y sY k))
        (fst (H̃ᶜʷ→ {C = X} {D = Y} k f) x)
      ≡ fst (H̃ˢᵏᵉˡ→ {C = fst sX} {D = fst sY} k
          (fst (snd sY) ∘ f ∘ invEq (snd sX)))
          (fst (fst (witness-comparison X sX k)) x)
  witness-comparison-natural X Y sX sY k f x =
    witness-comparison-action Y sY k
      (fst (H̃ᶜʷ→ {C = X} {D = Y} k f) x)
    ∙ substCommSlice B C F p x
    ∙ cong (F (PT.∣ sX ∣₁ , PT.∣ sY ∣₁))
        (sym (witness-comparison-action X sX k x))
    where
    W : Type₁
    W = isCW (fst X) × isCW (fst Y)

    B : W → Type
    B w = fst (H̃ᶜʷ (fst X , fst w) k)

    C : W → Type
    C w = fst (H̃ᶜʷ (fst Y , snd w) k)

    F : (w : W) → B w → C w
    F w = fst (H̃ᶜʷ→ {C = fst X , fst w} {D = fst Y , snd w} k f)

    p : Path (isCW (fst X) × isCW (fst Y))
      (snd X , snd Y) (PT.∣ sX ∣₁ , PT.∣ sY ∣₁)
    p i = PT.squash₁ (snd X) PT.∣ sX ∣₁ i
        , PT.squash₁ (snd Y) PT.∣ sY ∣₁ i
