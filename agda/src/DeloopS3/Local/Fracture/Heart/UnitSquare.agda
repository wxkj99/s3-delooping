{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Heart.UnitSquare where

-- The unit square with a specified unit homotopy.  Extending the actual chosen
-- loop/fibre filler avoids equating it with a separately chosen filler.
-- For cong-powLoop this is exactly RouteBWrap.loop-power-homotopy.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Nat using (ℕ)
open import DeloopS3.Local.Base using (F ; Local ; L ; η)
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.RouteB2 using (L-map)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (module Square)
open import DeloopS3.Local.Fracture.Heart.Squares

module Marked (n : ℕ) (A C : Type) (p : A → A) (r : C → C)
  (k : L n A → C) (ek : isEquiv k) (localC : Local n C)
  (h : (a : A) → k (η {n} {A} (p a)) ≡ r (k (η {n} {A} a))) where

  private
    u : A → L n A
    u = η {n} {A}
    q : L n A → L n A
    q = L-map n {A = A} {B = A} p
    d : A → C
    d = k ∘ u

  extended : (z : L n A) → k (q z) ≡ r (k z)
  extended = Unique.≡onη {F = F n} {X = A} {Y = C}
    localC (k ∘ q) (r ∘ k) h

  extended-β : (a : A) → extended (u a) ≡ h a
  extended-β a = refl

  abstract
    cartesian : Square.Cartesian A (L n A) A (L n A) u p q u (λ _ → refl)
      → Square.Cartesian A A C C p d d r h
    cartesian cart = subst
      (λ h' → Square.Cartesian A A C C p d d r h')
      (funExt λ a → cong sym (sym (rUnit (sym (h a)))))
      (transpose-cartesian A C A C d p r d
        (λ a → sym (extended (u a)) ∙ refl)
        (ReplaceRight.cartesian A (L n A) C u p q (k , ek) r extended
          (λ _ → refl) cart))
