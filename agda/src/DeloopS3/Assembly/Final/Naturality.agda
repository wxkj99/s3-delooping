{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.Final.Naturality where

-- Descend v(e⁻¹ ηa)=f⁻¹(κ ηa) to v e⁻¹=f⁻¹ κ by the localization
-- universal property into Y, then cancel e and f to obtain κ e=f v.
-- The specified unit square determines naturality, not merely agreement
-- on homotopy groups or an unspecified choice of inverse equivalence.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import DeloopS3.Local.Base using (F ; Local ; L ; η)
open import DeloopS3.Local.Unique using (module Unique)

-- A generic type former avoids normalizing the concrete geometric fibres
-- while merely forming the unit-level naturality statement.
UnitLoopSquare : (m : ℕ) (A X Y B : Type)
  → (X ≃ L m A) → (Y ≃ L 30 B) → (X → Y) → (A → B) → Type
UnitLoopSquare m A X Y B e f v U = (a : A)
  → Path Y (v (invEq e (η {m} {A} a))) (invEq f (η {30} {B} (U a)))

abstract
  unit-square-descent : (m : ℕ) (A X Y Z : Type)
    (e : X ≃ L m A) (f : Y ≃ Z) (v : X → Y) (κ : L m A → Z)
    → Local m Y
    → ((a : A) → v (invEq e (η {m} {A} a)) ≡ invEq f (κ (η {m} {A} a)))
    → (x : X) → κ (equivFun e x) ≡ equivFun f (v x)
  unit-square-descent m A X Y Z e f v κ lY on-unit x =
    sym (secEq f (κ (equivFun e x)))
      ∙ cong (equivFun f)
        (sym (all (equivFun e x)) ∙ cong v (retEq e x))
    where
    all : (z : L m A) → v (invEq e z) ≡ invEq f (κ z)
    all = Unique.≡onη {F = F m} {X = A} {Y = Y}
      lY (v ∘ invEq e) (invEq f ∘ κ) on-unit

  common-coordinate : (F A B S : Type)
    (a : F ≃ A) (b : F ≃ B) (σ : F ≃ S) (U : A → B)
    → ((z : F) → U (equivFun a z) ≡ equivFun b z)
    → (x : A) → equivFun σ (invEq b (U x)) ≡ equivFun σ (invEq a x)
  common-coordinate F A B S a b σ U h x = cong (equivFun σ)
    (cong (invEq b) (sym (cong U (secEq a x)) ∙ h (invEq a x))
      ∙ retEq b (invEq a x))
