{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Heart where

-- Locality of localization fibres from the arithmetic power square.
-- The cartesian power square gives locality of the connected based fibre;
-- connectedness of L_n X propagates this proposition along mere paths.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Loopspace using (Ω)
open import DeloopS3.Local.Base using (Local ; L ; η)
open import DeloopS3.Local.RouteB1.Closure using (local-prop)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (SC ; connected-prop-elim)
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout)
open import DeloopS3.Local.Fracture.Heart.Based using (module UnitFibre)

abstract
  coprime-unit-fibres-local : (m n : ℕ) (X : Pointed ℓ-zero)
    → SC (typ X) → SC (typ (Ω X)) → Bezout m n
    → (y : L n (typ X)) → Local m (fiber (η {n} {typ X}) y)
  coprime-unit-fibres-local m n X scX scH bez =
    connected-prop-elim (L n (typ X) , η {n} {typ X} (pt X))
      (UnitFibre.localized-connected m n X scX scH bez)
      (λ y → Local m (fiber (η {n} {typ X}) y))
      (λ y → local-prop {m = m} {A = fiber (η {n} {typ X}) y})
      (UnitFibre.based-local m n X scX scH bez)
