{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TotalWindowSquare where

open import Cubical.Foundations.Prelude

rebase-square : ∀ {ℓ} {X : Type ℓ} {A B C D E : X}
  (p : A ≡ B) (q : C ≡ D) (a : A ≡ C) (b : B ≡ D)
  (c : C ≡ E) → Square p q a b
  → Square (sym a ∙ p) (sym c ∙ q) c b
rebase-square p q a b c S t s =
  hcomp (λ k → λ
    { (t = i0) → (sym a ∙ p) s
    ; (t = i1) → compPath-filler' (sym c) q k s
    ; (s = i0) → c (t ∧ k)
    ; (s = i1) → b t }) (S0 t s)
  where
  S0 : Square (sym a ∙ p) q refl b
  S0 t s = hcomp (λ k → λ
    { (t = i0) → compPath-filler' (sym a) p k s
    ; (t = i1) → q s
    ; (s = i0) → a (t ∨ k)
    ; (s = i1) → b t }) (S t s)
