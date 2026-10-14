{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Fibers where

-- Localization of fibres.  The equivalences below keep the actual
-- fiber-unit and the generator computation of Unique.≡onη.
open import DeloopS3.Local.RouteB2.Common
open import DeloopS3.Local.RouteB2.Finite
open import DeloopS3.Local.RouteB2.Families
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.Telescope using (pow∙ ; module LocalizationUnit)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-cong-equiv ; Σ-cong-equiv-snd)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
import Cubical.Functions.Fibration as Fib
import Cubical.HITs.Localization.Properties as Loc

-- Cancellation with a specified unit, not just an equivalence of types.
local-equivalence-from-unit : (m : ℕ) {A B : Type}
  (u : A → B) (e : B ≃ L m A)
  → ((a : A) → equivFun e (u a) ≡ η a) → LocalEquiv m u
local-equivalence-from-unit m {A} {B} u e β Z lZ =
  second-in-isEquiv-comp→isEquiv
    (λ (h : L m A → Z) → h ∘ equivFun e)
    (λ (h : B → Z) → h ∘ u)
    (λ (h : L m A → Z) → h ∘ η)
    (snd (preCompEquiv e)) (Unique.isEquiv-preη lZ)
    (funExt λ h → funExt λ a → cong h (sym (β a)))

fiber-unit : (m : ℕ) {E B : Type} (f : E → B) (b : B)
  → fiber f b → fiber (L-map m f) (η b)
fiber-unit m f b (e , p) = η e , cong η p

module Comparison (H : RouteB1-Hypotheses) where
  open RouteB1-Hypotheses H

  fiber-target-local : (m : ℕ) {E B : Type} (f : E → B) (b : B)
    → Local m (fiber (L-map m f) (η b))
  fiber-target-local m f b = local-fiber (local-L m _) (local-L m _) (L-map m f) (η b)

  fiber-comparison : (m : ℕ) {E B : Type} (f : E → B) (b : B)
    → L m (fiber f b) → fiber (L-map m f) (η b)
  fiber-comparison m f b = Loc.rec (fiber-target-local m f b) (fiber-unit m f b)

  fiber-comparison-β : (m : ℕ) {E B : Type} (f : E → B) (b : B)
    → (u : fiber f b) → fiber-comparison m f b (η u) ≡ fiber-unit m f b u
  fiber-comparison-β m f b u = refl

module Preservation (H : RouteB1-Hypotheses)
  (loop-power-derivative : (m : ℕ) (X : Pointed ℓ-zero)
    → (q : typ (Ω (Ω X))) → fst (Ω→ (pow∙ m X)) q ≡ powLoop m q)
  where
  open Reflection H loop-power-derivative
  open Total H loop-power-derivative
  open Comparison H public

  module FiberProof (m : ℕ) {E B : Type} (f : E → B) (sc : SC B) where
    P : B → Type
    P = fiber f

    -- Represent f by its family of fibres, BEFORE extending the unit.
    -- This makes the comparison from L E compute strictly on η e.
    u : E → TotalQ m B P
    u = family-unit m B P ∘ equivFun (Fib.totalEquiv f)

    u-local-equivalence : LocalEquiv m u
    u-local-equivalence Z lZ = snd (compEquiv
      ((λ h → h ∘ family-unit m B P) , family-unit-local-equivalence m B P Z lZ)
      (preCompEquiv (Fib.totalEquiv f)))

    forward : L m E → TotalQ m B P
    forward = Loc.rec (family-total-local m B P sc) u

    -- The maps must compute on units; their equivalence witnesses need
    -- not unfold while checking the path inverses in fiber-code-β-refl.
    abstract
      forward-isEquiv : isEquiv forward
      forward-isEquiv = snd (LocalizationUnit.equivalence u
        (family-total-local m B P sc) u-local-equivalence)

      c-isEquiv : isEquiv (S-to-L m {B})
      c-isEquiv = S-to-L-isEquiv m sc

    h : L m E ≃ TotalQ m B P
    h = forward , forward-isEquiv

    c : S m B ≃ L m B
    c = S-to-L m , c-isEquiv

    unit-square : (z : L m E) → equivFun c (fst (equivFun h z)) ≡ L-map m f z
    unit-square = Unique.≡onη (local-L m B)
      (equivFun c ∘ fst ∘ equivFun h) (L-map m f) (λ _ → refl)

    unit-square-β : (e : E) → unit-square (η e) ≡ refl
    unit-square-β e = refl

    reindex-total : (b : B) → fiber (L-map m f) (η b)
      ≃ fiber (λ (t : TotalQ m B P) → equivFun c (fst t)) (η b)
    reindex-total b = Σ-cong-equiv h (λ z → compPathlEquiv (unit-square z))

    reindex-base : (b : B)
      → fiber (λ (t : TotalQ m B P) → equivFun c (fst t)) (η b)
      ≃ fiber (λ (t : TotalQ m B P) → fst t) (ηS b)
    reindex-base b = Σ-cong-equiv-snd (λ (t : TotalQ m B P) →
      invEquiv (congEquiv {x = fst t} {y = ηS b} c))

    fiber-code : (b : B) → fiber (L-map m f) (η b) ≃ L m (fiber f b)
    fiber-code b = compEquiv (reindex-total b)
      (compEquiv (reindex-base b) (Fib.fiberEquiv (Q m B P) (ηS b)))

    fiber-code-β-refl : (e : E)
      → equivFun (fiber-code (f e)) (fiber-unit m f (f e) (e , refl)) ≡ η (e , refl)
    fiber-code-β-refl e =
      cong (λ p → subst (Q m B P) p (η (e , refl)))
        (cong (invEq ce) (sym (lUnit refl)) ∙ retEq ce refl)
      ∙ transportRefl (η (e , refl))
      where
      ce : (ηS {m = m} (f e) ≡ ηS (f e)) ≃ (η {m = m} (f e) ≡ η (f e))
      ce = congEquiv c

    fiber-code-β : (b : B) (v : fiber f b)
      → equivFun (fiber-code b) (fiber-unit m f b v) ≡ η v
    fiber-code-β b (e , p) = J
      (λ b p → equivFun (fiber-code b) (fiber-unit m f b (e , p)) ≡ η (e , p))
      (fiber-code-β-refl e) p

  fiber-unit-local-equivalence : (m : ℕ) {E B : Type}
    (f : E → B) (b : B) → SC B → LocalEquiv m (fiber-unit m f b)
  fiber-unit-local-equivalence m f b sc = local-equivalence-from-unit m
    (fiber-unit m f b) (FiberProof.fiber-code m f sc b) (FiberProof.fiber-code-β m f sc b)

  localization-preserves-fiber : (m : ℕ) {E B : Type}
    (f : E → B) (b : B) → SC B → isEquiv (fiber-comparison m f b)
  localization-preserves-fiber m f b sc = snd
    (LocalizationUnit.equivalence (fiber-unit m f b) (fiber-target-local m f b)
      (fiber-unit-local-equivalence m f b sc))
