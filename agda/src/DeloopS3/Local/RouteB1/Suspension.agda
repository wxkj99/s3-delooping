{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB1.Suspension where

-- Suspended localization and its universal property.  The suspended reflector is
-- the existing localization HIT, not an assumed separated modality.
open import DeloopS3.Local.Base using (Local ; deg₁)
open import DeloopS3.Local.Powers using (degSphere)
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.RouteB1.Closure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.PathSplit using
  (toIsEquiv ; fromIsEquiv ; isPropIsPathSplitEquiv)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (univalence)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd ; Σ≡PropEquiv)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Susp.Base using (Susp ; north ; south ; merid)
open import Cubical.HITs.Susp.Properties using (funSpaceSuspIso)
import Cubical.HITs.Localization.Base as Localization

SF : ℕ → Unit → Susp S¹ → Susp S¹
SF m _ = degSphere m 1

SLocal : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
SLocal m A = Localization.isLocal (SF m) A

S : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
S m A = Localization.Localize (SF m) A

ηS : ∀ {ℓ m} {A : Type ℓ} → A → S m A
ηS = Localization.∣_∣

slocal-prop : ∀ {ℓ m} {A : Type ℓ} → isProp (SLocal m A)
slocal-prop = isPropΠ λ _ → isPropIsPathSplitEquiv _

separated-prop : ∀ {ℓ m} {A : Type ℓ} → isProp (Separated m A)
separated-prop = isPropΠ λ _ → isPropΠ λ _ → local-prop

-- The same proof as Powers.susp-preEquiv, explicitly at all universes.
separated→slocal : ∀ {ℓ m} {A : Type ℓ}
  → Separated m A → SLocal m A
separated→slocal {m = m} {A = A} sepA _ = fromIsEquiv _
  (subst isEquiv agrees (snd conjugate))
  where
  total : (Σ[ x ∈ A ] Σ[ y ∈ A ] (S¹ → x ≡ y))
    ≃ (Σ[ x ∈ A ] Σ[ y ∈ A ] (S¹ → x ≡ y))
  total = Σ-cong-equiv-snd λ x → Σ-cong-equiv-snd λ y →
    (λ h → h ∘ deg₁ m) , localᵘ→preEquiv (sepA x y)

  conjugate : (Susp S¹ → A) ≃ (Susp S¹ → A)
  conjugate = compEquiv (isoToEquiv (invIso funSpaceSuspIso))
    (compEquiv total (isoToEquiv funSpaceSuspIso))

  agrees : fst conjugate ≡ (λ h → h ∘ SF m tt)
  agrees = funExt λ h → funExt λ
    { north → refl ; south → refl ; (merid a i) → refl }

slocal→separated : ∀ {ℓ m} {A : Type ℓ}
  → SLocal m A → Separated m A
slocal→separated {m = m} {A = A} lA x y = preEquiv→localᵘ
  (fiberEquiv (λ y → S¹ → x ≡ y) (λ y → S¹ → x ≡ y)
    (λ y h → h ∘ deg₁ m) (outer x) y)
  where
  conjugate : (Σ[ x ∈ A ] Σ[ y ∈ A ] (S¹ → x ≡ y))
    ≃ (Σ[ x ∈ A ] Σ[ y ∈ A ] (S¹ → x ≡ y))
  conjugate = compEquiv (isoToEquiv funSpaceSuspIso)
    (compEquiv ((λ h → h ∘ SF m tt) , toIsEquiv _ (lA tt))
      (isoToEquiv (invIso funSpaceSuspIso)))

  outer : (x : A) → isEquiv
    (λ (v : Σ[ y ∈ A ] (S¹ → x ≡ y)) → fst v , snd v ∘ deg₁ m)
  outer = fiberEquiv (λ x → Σ[ y ∈ A ] (S¹ → x ≡ y))
    (λ x → Σ[ y ∈ A ] (S¹ → x ≡ y))
    (λ x v → fst v , snd v ∘ deg₁ m) (snd conjugate)

susp-locality : ∀ {ℓ} (m : ℕ) (A : Type ℓ)
  → SLocal m A ≃ Separated m A
susp-locality m A = propBiimpl→Equiv slocal-prop separated-prop
  slocal→separated separated→slocal

slocal-S : ∀ {ℓ} (m : ℕ) (X : Type ℓ) → SLocal m (S m X)
slocal-S m X = Localization.isLocal-Localize (SF m) X

separated-S : ∀ {ℓ} (m : ℕ) (X : Type ℓ) → Separated m (S m X)
separated-S m X = slocal→separated (slocal-S m X)

-- Ordinary UP only; the restricted dependent UP is derived in Sections.
S-preη-isEquiv : ∀ {ℓ ℓ' m} {X : Type ℓ} {A : Type ℓ'}
  → Separated m A
  → isEquiv (λ (h : S m X → A) → h ∘ ηS)
S-preη-isEquiv sepA = Unique.isEquiv-preη (separated→slocal sepA)

LocalUniverse : ℕ → Type₁
LocalUniverse m = Σ[ A ∈ Type ] Local m A

local-universe-separated : (m : ℕ) → Separated m (LocalUniverse m)
local-universe-separated m U V = local-equiv paths
  (local-subtype (local-function (snd V)) (λ f → isPropIsEquiv f))
  where
  paths : (fst U ≃ fst V) ≃ (U ≡ V)
  paths = compEquiv (invEquiv univalence)
    (Σ≡PropEquiv (λ _ → local-prop))
