{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Families where

-- Localization of families and total spaces over a simply connected base.
-- Only the base is simply connected.
open import DeloopS3.Local.RouteB2.Common
open import DeloopS3.Local.RouteB2.Finite
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.Telescope using (pow∙ ; module LocalizationUnit)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (ΣPathP ; Σ-cong-equiv ; Σ-Π-Iso)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.Homotopy.Connected using (isConnectedPath)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Localization.Properties as Loc

SC-circle-merely-constant : {B : Type} → SC B → (g : S¹ → B)
  → PT.∥ g ≡ (λ _ → g base) ∥₁
SC-circle-merely-constant sc g = PT.map
  (λ p → sym (Iso.ret freeIso g)
    ∙ cong (Iso.inv freeIso) (ΣPathP (refl , p))
    ∙ Iso.ret freeIso (λ _ → g base))
  (connected-mere-path (isConnectedPath 2 sc (g base) (g base)) (cong g loop) refl)

local-Σ-SC : (m : ℕ) {B : Type} {P : B → Type}
  → SC B → Local m B → ((b : B) → Local m (P b))
  → Local m (Σ B P)
local-Σ-SC m {B} {P} sc lB lP = preEquiv→local (snd conjugate)
  where
  Sections : (S¹ → B) → Type
  Sections g = (s : S¹) → P (g s)

  ρ : (g : S¹ → B) → Sections g → Sections (g ∘ deg₁ m)
  ρ g h = h ∘ deg₁ m

  ρ-equiv : (g : S¹ → B) → isEquiv (ρ g)
  ρ-equiv g = PT.rec (isPropIsEquiv (ρ g))
    (λ p → subst (λ g → isEquiv (ρ g)) (sym p)
      (local→preEquiv (lP (g base))))
    (SC-circle-merely-constant sc g)

  total : (Σ (S¹ → B) Sections) ≃ (Σ (S¹ → B) Sections)
  total = Σ-cong-equiv ((λ g → g ∘ deg₁ m) , local→preEquiv lB)
    (λ g → ρ g , ρ-equiv g)

  conjugate : (S¹ → Σ B P) ≃ (S¹ → Σ B P)
  conjugate = compEquiv (isoToEquiv Σ-Π-Iso)
    (compEquiv total (isoToEquiv (invIso Σ-Π-Iso)))

Σ-unit-local-equivalence : (m : ℕ) (B : Type) (P : B → Type)
  → LocalEquiv m {B = Σ[ b ∈ B ] L m (P b)}
      (λ (u : Σ B P) → fst u , η {m} (snd u))
Σ-unit-local-equivalence m B P Z lZ = isoToIsEquiv
  (iso restrict extend (λ _ → refl) ret-law)
  where
  restrict : (Σ[ b ∈ B ] L m (P b) → Z) → (Σ B P → Z)
  restrict h (b , p) = h (b , η p)
  extend : (Σ B P → Z) → (Σ[ b ∈ B ] L m (P b) → Z)
  extend h (b , t) = Loc.rec lZ (λ p → h (b , p)) t
  ret-law : (h : Σ[ b ∈ B ] L m (P b) → Z) → extend (restrict h) ≡ h
  ret-law h = funExt λ { (b , t) → Unique.≡onη lZ
    (Loc.rec lZ (λ p → h (b , η p))) (λ t → h (b , t)) (λ _ → refl) t }

module Extension (H : RouteB1-Hypotheses) where
  open Suspended H

  Q-code : (m : ℕ) (B : Type) (P : B → Type) → S m B → LocalUniverse m
  Q-code m B P = S-rec (local-universe-separated m)
    (λ b → L m (P b) , local-L m (P b))

  Q : (m : ℕ) (B : Type) (P : B → Type) → S m B → Type
  Q m B P t = fst (Q-code m B P t)

  Q-local : (m : ℕ) (B : Type) (P : B → Type) (t : S m B)
    → Local m (Q m B P t)
  Q-local m B P t = snd (Q-code m B P t)

  Q-β : (m : ℕ) (B : Type) (P : B → Type) (b : B)
    → Q m B P (ηS b) ≡ L m (P b)
  Q-β m B P b = refl

  TotalQ : (m : ℕ) (B : Type) (P : B → Type) → Type
  TotalQ m B P = Σ (S m B) (Q m B P)

  family-unit : (m : ℕ) (B : Type) (P : B → Type) → Σ B P → TotalQ m B P
  family-unit m B P (b , p) = ηS b , η p

  family-unit-local-equivalence : (m : ℕ) (B : Type) (P : B → Type)
    → LocalEquiv m (family-unit m B P)
  family-unit-local-equivalence m B P Z lZ = snd (compEquiv
    ((λ h u → h (ηS (fst u) , snd u)) , S-unit-base-change m B (Q m B P) Z lZ)
    ((λ h u → h (fst u , η (snd u))) , Σ-unit-local-equivalence m B P Z lZ))

module Total (H : RouteB1-Hypotheses)
  (loop-power-derivative : (m : ℕ) (X : Pointed ℓ-zero)
    → (q : typ (Ω (Ω X))) → fst (Ω→ (pow∙ m X)) q ≡ powLoop m q)
  where
  open Reflection H loop-power-derivative
  open Extension H public

  family-total-local : (m : ℕ) (B : Type) (P : B → Type)
    → SC B → Local m (TotalQ m B P)
  family-total-local m B P sc = local-Σ-SC m
    (S-preserves-SC m sc) (local-S-SC m sc) (Q-local m B P)

  family-total-localization : (m : ℕ) (B : Type) (P : B → Type)
    → SC B → Σ[ e ∈ L m (Σ B P) ≃ TotalQ m B P ]
      (equivFun e ∘ η ≡ family-unit m B P)
  family-total-localization m B P sc =
    LocalizationUnit.equivalence (family-unit m B P)
      (family-total-local m B P sc) (family-unit-local-equivalence m B P) , refl
