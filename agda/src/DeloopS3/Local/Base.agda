{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Base where

-- Degree-m circle localization, its unit, locality, and local equivalences.
-- The arithmetic interpretation assumes m > 0; the kernel needs no such
-- assumption. Only the single degree-m circle map is localized.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit using (toIsEquiv ; fromIsEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
import Cubical.HITs.Localization.Base as Localization
import Cubical.HITs.PropositionalTruncation as PT

powLoop : ∀ {ℓ} {X : Type ℓ} {x : X} → ℕ → x ≡ x → x ≡ x
powLoop zero p = refl
powLoop (suc r) p = p ∙ powLoop r p

deg₁ : ℕ → S¹ → S¹
deg₁ m base = base
deg₁ m (loop i) = powLoop m loop i

F : ℕ → Unit → S¹ → S¹
F m _ = deg₁ m

L : ℕ → Type → Type
L m X = Localization.Localize (F m) X

η : ∀ {m X} → X → L m X
η = Localization.∣_∣

Local : ℕ → Type → Type
Local m X = Localization.isLocal (F m) X

local-L : (m : ℕ) (X : Type) → Local m (L m X)
local-L m X = Localization.isLocal-Localize (F m) X

local→preEquiv : ∀ {m X} → Local m X
  → isEquiv (λ (g : S¹ → X) → g ∘ deg₁ m)
local→preEquiv h = toIsEquiv _ (h tt)

preEquiv→local : ∀ {m X}
  → isEquiv (λ (g : S¹ → X) → g ∘ deg₁ m) → Local m X
preEquiv→local h _ = fromIsEquiv _ h

MerelyNull : {X Y : Type} → (X → Y) → Type
MerelyNull {Y = Y} f = PT.∥ Σ[ y ∈ Y ] (f ≡ (λ _ → y)) ∥₁

LocalEquiv : (m : ℕ) {A B : Type} → (A → B) → Type₁
LocalEquiv m {B = B} f = (Z : Type) → Local m Z
  → isEquiv (λ (g : B → Z) → g ∘ f)
