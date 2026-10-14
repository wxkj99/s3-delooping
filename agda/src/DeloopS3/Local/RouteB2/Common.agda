{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Common where

-- Interfaces for localization and its suspended reflector.
-- RouteB1 supplies the locality, separatedness, and base-change inputs.
open import DeloopS3.Local.Base public
open import DeloopS3.Local.Powers public
open import DeloopS3.Local.Unique using (module Unique)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Susp.Base using (Susp)
import Cubical.HITs.Localization.Base as Loc
import Cubical.HITs.Localization.Properties as Loc
open import Cubical.Homotopy.Connected using (isConnected)

Localᵘ : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
Localᵘ m A = Loc.isLocal (F m) A

Separated : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
Separated m A = (a b : A) → Localᵘ m (a ≡ b)

SF : ℕ → Unit → Susp S¹ → Susp S¹
SF m _ = degSphere m 1

SLocal : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
SLocal m A = Loc.isLocal (SF m) A

S : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
S m A = Loc.Localize (SF m) A

ηS : ∀ {ℓ m} {A : Type ℓ} → A → S m A
ηS = Loc.∣_∣

LocalUniverse : ℕ → Type₁
LocalUniverse m = Σ[ A ∈ Type ] Local m A

Conn SC : ∀ {ℓ} → Type ℓ → Type ℓ
Conn = isConnected 2
SC = isConnected 3

L-map : (m : ℕ) {A B : Type} → (A → B) → L m A → L m B
L-map m f = Loc.rec (local-L m _) (η ∘ f)

record RouteB1-Hypotheses : Typeω where
  field
    susp-locality : ∀ {ℓ} (m : ℕ) (A : Type ℓ)
      → SLocal m A ≃ Separated m A
    local-fiber : ∀ {ℓ ℓ' m} {A : Type ℓ} {B : Type ℓ'}
      → Localᵘ m A → Localᵘ m B → (f : A → B) → (b : B)
      → Localᵘ m (fiber f b)
    local-universe-separated : (m : ℕ)
      → Separated m (LocalUniverse m)
    S-unit-base-change : (m : ℕ) (X : Type) (P : S m X → Type)
      → LocalEquiv m {B = Σ (S m X) P}
          (λ (u : Σ[ x ∈ X ] P (ηS x))
            → ηS {m = m} {A = X} (fst u) , snd u)

module Suspended (H : RouteB1-Hypotheses) where
  open RouteB1-Hypotheses H public

  separated-S : (m : ℕ) (X : Type) → Separated m (S m X)
  separated-S m X = equivFun (susp-locality m _) (Loc.isLocal-Localize (SF m) X)

  separated→SLocal : ∀ {ℓ m} {X : Type ℓ} → Separated m X → SLocal m X
  separated→SLocal {m = m} = invEq (susp-locality m _)

  S-rec : ∀ {ℓ ℓ' m} {X : Type ℓ} {Y : Type ℓ'}
    → Separated m Y → (X → Y) → S m X → Y
  S-rec sep = Loc.rec (separated→SLocal sep)

  S-unique : ∀ {ℓ ℓ' m} {X : Type ℓ} {Y : Type ℓ'}
    → Separated m Y → (f g : S m X → Y)
    → ((x : X) → f (ηS x) ≡ g (ηS x)) → f ≡ g
  S-unique sep = Unique.unique (separated→SLocal sep)
