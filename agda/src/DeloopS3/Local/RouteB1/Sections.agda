{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB1.Sections where

-- Dependent universal properties.  Both rows of the mapping-space
-- square are ordinary UPs; taking their fibres gives the dependent UP.
open import DeloopS3.Local.Base using (Local ; LocalEquiv)
open import DeloopS3.Local.RouteB1.Closure
open import DeloopS3.Local.RouteB1.Suspension
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using
  (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-cong-equiv ; Σ-Π-≃ ; curryEquiv)
import Cubical.Functions.Fibration as Fibration

module SectionFibres where
  -- The forward map is literally s ↦ ((λ d → (g d , s d)) , refl).
  -- First use the fibre of a projection, then uncurry maps into a sum.
  section-fiber-equiv : ∀ {ℓD ℓB ℓP} {D : Type ℓD} {B : Type ℓB}
    (P : B → Type ℓP) (g : D → B)
    → ((d : D) → P (g d))
      ≃ fiber (λ (h : D → Σ B P) → fst ∘ h) g
  section-fiber-equiv {D = D} P g =
    compEquiv
      (invEquiv (Fibration.fiberEquiv (λ h → (d : D) → P (h d)) g))
      (Σ-cong-equiv (invEquiv Σ-Π-≃) (λ h → idEquiv (fst h ≡ g)))

S-unit-sections : (m : ℕ) (X : Type) (P : S m X → Type)
  → ((t : S m X) → Local m (P t))
  → isEquiv (λ (s : (t : S m X) → P t) (x : X) → s (ηS x))
S-unit-sections m X P lP =
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ s x → s (ηS x))
    target (snd (compEquiv source restricted))
  where
  unit : X → S m X
  unit = ηS

  source = SectionFibres.section-fiber-equiv P (idfun (S m X))
  target = SectionFibres.section-fiber-equiv P unit

  -- The top row uses separatedness of the total space; the bottom row
  -- uses separatedness of S m X.  No dependent HIT eliminator is used.
  restricted = MappingFibres.restriction-equiv unit
    (λ (u : Σ (S m X) P) → fst u) (idfun (S m X))
    (S-preη-isEquiv (separated-Σ-local (separated-S m X) lP))
    (S-preη-isEquiv (separated-S m X))

S-unit-base-change : (m : ℕ) (X : Type) (P : S m X → Type)
  → LocalEquiv m
      (λ (u : Σ[ x ∈ X ] P (ηS x))
        → ηS {m = m} {A = X} (fst u) , snd u)
S-unit-base-change m X P Z lZ = snd
  (compEquiv curryEquiv (compEquiv restricted (invEquiv curryEquiv)))
  where
  -- P itself need not be local.  Only the function fibres P t → Z are.
  restricted : ((t : S m X) → P t → Z)
    ≃ ((x : X) → P (ηS x) → Z)
  restricted = (λ s x → s (ηS x)) ,
    S-unit-sections m X (λ t → P t → Z) (λ t → local-function lZ)
