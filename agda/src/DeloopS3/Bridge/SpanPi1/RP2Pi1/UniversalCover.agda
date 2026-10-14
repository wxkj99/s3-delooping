{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.RP2Pi1.UniversalCover where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Connected using (isConnected; isConnectedPath)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.Truncation as TR

-- Only set-truncated paths are chosen. The actual total space need not
-- be contractible: simple connectedness is precisely what is required.
module SimplyConnectedCover {B : Type₀} (F : B → Type₀)
  (setF : (x : B) → isSet (F x))
  (connected : isConnected 3 (Σ B F))
  (b : B) (a : F b) where

  encode : (x : B) → ST.∥ b ≡ x ∥₂ → F x
  encode x = ST.rec (setF x) (λ p → subst F p a)

  private
    project : {x : B} {z : F x}
      → TR.∥ Path (Σ B F) (b , a) (x , z) ∥ 2
      → ST.∥ b ≡ x ∥₂
    project = TR.rec ST.squash₂ (λ p → ST.∣ cong fst p ∣₂)

    paths : (x : B) (z : F x)
      → isContr (TR.∥ Path (Σ B F) (b , a) (x , z) ∥ 2)
    paths x z = isConnectedPath 2 connected (b , a) (x , z)

  decode : (x : B) → F x → ST.∥ b ≡ x ∥₂
  decode x z = project (paths x z .fst)

  private
    encode-project : {x : B} {z : F x}
      → (p : TR.∥ Path (Σ B F) (b , a) (x , z) ∥ 2)
      → encode x (project p) ≡ z
    encode-project {x} {z} = TR.elim
      (λ _ → isProp→isSet (setF x _ z))
      (λ p → fromPathP (λ i → p i .snd))

    pathLift : {x : B} (p : b ≡ x)
      → Path (Σ B F) (b , a) (x , subst F p a)
    pathLift p i = p i , transport-filler (cong F p) a i

  abstract
    encode-decode : (x : B) (z : F x) → encode x (decode x z) ≡ z
    encode-decode x z = encode-project (paths x z .fst)

    decode-encode : (x : B) (p : ST.∥ b ≡ x ∥₂)
      → decode x (encode x p) ≡ p
    decode-encode x = ST.elim
      (λ _ → isProp→isSet (ST.squash₂ _ _))
      (λ p → cong project (paths x (subst F p a) .snd TR.∣ pathLift p ∣))

  pathEquiv : (x : B) → ST.∥ b ≡ x ∥₂ ≃ F x
  pathEquiv x = isoToEquiv
    (iso (encode x) (decode x) (encode-decode x) (decode-encode x))
