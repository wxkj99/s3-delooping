{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Heart.PowerSquare where

-- The cartesian power square for the arithmetic fibre argument.
-- The marked universal property is applied to the supplied filler.  This retains, in
-- particular, LoopedFiber.powerNaturality without a new coherence premise.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import DeloopS3.Local.Base using (Local ; L ; η ; local-L ; powLoop)
open import DeloopS3.Local.Powers using (local-path)
open import DeloopS3.Local.RouteB2 using
  (L-map ; path-comparison ; path-comparison-isEquiv ; L∙ ; η∙ ; unit-loop-normalize)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (SC ; module Square)
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout)
open import DeloopS3.Local.Fracture.Arithmetic.PowerFibres using (coprime-power-fibres-local)
open import DeloopS3.Local.Fracture.RouteBWrap using (localize-power-square)
open import DeloopS3.Local.Fracture.Heart.UnitSquare using (module Marked)

module PowerSquare (m n : ℕ) (X : Pointed ℓ-zero)
  (scX : SC (typ X)) (scH : SC (typ (Ω X))) (bez : Bezout m n) where

  private
    A : Type
    A = pt X ≡ pt X
    C : Type
    C = η {n} {typ X} (pt X) ≡ η {n} {typ X} (pt X)
    p : A → A
    p = powLoop {X = typ X} {x = pt X} m
    r : C → C
    r = powLoop {X = L n (typ X)} {x = η {n} {typ X} (pt X)} m
    k : L n A → C
    k = path-comparison n {X = typ X} (pt X) (pt X)
    raw : A → C
    raw = cong {A = typ X} {B = λ _ → L n (typ X)}
      {x = pt X} {y = pt X} (η {n} {typ X})

  -- No proof of Route B is unfolded at a specialization boundary.
  abstract
    localized-square : Square.Cartesian A (L n A) A (L n A)
      (η {n} {A}) p (L-map n {A = A} {B = A} p) (η {n} {A}) (λ _ → refl)
    localized-square = localize-power-square n m X scH
      (coprime-power-fibres-local X m n scH bez)

    comparison-isEquiv : isEquiv k
    comparison-isEquiv = path-comparison-isEquiv n {X = typ X} scX (pt X) (pt X)

    target-local : Local n C
    target-local = local-path {m = n} {X = L n (typ X)} (local-L n (typ X))
      (η {n} {typ X} (pt X)) (η {n} {typ X} (pt X))

  AllSquares : (A → C) → Type
  AllSquares d = (h : (a : A) → d (p a) ≡ r (d a))
    → Square.Cartesian A A C C p d d r h

  abstract
    raw-squares : AllSquares raw
    raw-squares h = Marked.cartesian n A C p r k comparison-isEquiv target-local h
      localized-square

    -- Transport the whole filler-indexed assertion, not just its four sides.
    -- The exact chosen powerNaturality can therefore be used at the endpoint.
    pointed-squares : AllSquares (fst (Ω→ {A = X} {B = L∙ n X} (η∙ n X)))
    pointed-squares = subst AllSquares
      (sym (funExt (unit-loop-normalize n X))) raw-squares
