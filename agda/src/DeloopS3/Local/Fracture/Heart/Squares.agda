{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Heart.Squares where

-- Finite changes of pullback squares for the arithmetic fibre argument.
-- The filler is carried through the pullback equivalence, never discarded.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Sigma using (Σ-cong-equiv ; Σ-cong-equiv-snd)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (PB ; module Square)

module ReplaceRight (A B C : Type) (u : A → B) (p : A → A)
  (q : B → B) (e : B ≃ C) (r : C → C)
  (H : (b : B) → fst e (q b) ≡ r (fst e b)) where

  private
    target : PB {A = B} {B = A} {C = B} q u
      ≃ PB {A = C} {B = A} {C = C} r (fst e ∘ u)
    target = Σ-cong-equiv e λ b → Σ-cong-equiv-snd λ a →
      compEquiv (congEquiv {x = q b} {y = u a} e)
        (compPathlEquiv (sym (H b)))

  abstract
    cartesian : (h : (a : A) → q (u a) ≡ u (p a))
      → Square.Cartesian A B A B u p q u h
      → Square.Cartesian A C A C (fst e ∘ u) p r (fst e ∘ u)
          (λ a → sym (H (u a)) ∙ cong (fst e) (h a))
    cartesian h cart = snd (compEquiv
      (Square.gap A B A B u p q u h , cart) target)

abstract
  transpose-cartesian : (A A' B B' : Type)
    (u : A → A') (f : A → B) (f' : A' → B') (v : B → B')
    (h : (a : A) → f' (u a) ≡ v (f a))
    → Square.Cartesian A A' B B' u f f' v h
    → Square.Cartesian A B A' B' f u v f' (λ a → sym (h a))
  transpose-cartesian A A' B B' u f f' v h cart =
    snd (compEquiv (Square.gap A A' B B' u f f' v h , cart)
      (isoToEquiv swap))
    where
    swap : Iso (PB {A = A'} {B = B} {C = B'} f' v)
      (PB {A = B} {B = A'} {C = B'} v f')
    Iso.fun swap (a , b , p) = b , a , sym p
    Iso.inv swap (b , a , p) = a , b , sym p
    Iso.sec swap _ = refl
    Iso.ret swap _ = refl
