{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.PowerFibres where

-- Power equivalences on fibres from the double-loop matrix theorem.
-- The derivative is needed only as a homotopy of the underlying maps.
-- Transporting the chosen square along it produces SOME filler, to which
-- the universally quantified double-loop matrix theorem applies.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.Homotopy.Connected using (isConnectedSubtr)
open import DeloopS3.Local.Base using (Local ; powLoop)
open import DeloopS3.Local.Telescope using (pow∙)
open import DeloopS3.Local.RouteB1.Closure using (local-prop)
open import DeloopS3.Local.RouteB2.Derivative using (loop-power-derivative)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout ; double-power-square)
open import DeloopS3.Local.Fracture.Arithmetic.LoopFiber using (module LoopedFiber)

module PowerFibre (X : Pointed ℓ-zero) (m n : ℕ)
  (sc : SC (typ (Ω X))) (bez : Bezout m n) where
  private
    H : Pointed ℓ-zero
    H = Ω X
    Y : Type
    Y = typ (Ω H)
    pm : Y → Y
    pm = powLoop {X = typ H} {x = pt H} m
    pn : Y → Y
    pn = powLoop {X = typ H} {x = pt H} n

    module LF = LoopedFiber H H (pow∙ m X)

    -- This family quantifies over every filler.  Consequently transport
    -- does not impose a higher equation on loop-power-derivative.
    AllSquares : (Y → Y) → Type
    AllSquares d = (h : (z : Y) → d (pn z) ≡ pn (d z))
      → Square.Cartesian Y Y Y Y pn d d pn h

    derivative-squares : AllSquares LF.d
    derivative-squares = subst AllSquares
      (sym (funExt (loop-power-derivative m X)))
      (double-power-square X m n bez)

    connH : Conn (typ H)
    connH = isConnectedSubtr 2 1 sc

    connW : Conn (typ LF.W)
    connW = connected-fiber-SC-base
      (powLoop {X = typ X} {x = pt X} m) connH sc (pt H)

    based : Local n (typ LF.W)
    based = connected-based-powers→local n LF.W connW
      (LF.cartesian-power→loop-power n (derivative-squares (LF.powerNaturality n)))

  coprime-power-fibres-local : (h : typ (Ω X))
    → Local n (fiber (powLoop {X = typ X} {x = pt X} m) h)
  coprime-power-fibres-local = connected-prop-elim H connH
    (λ h → Local n (fiber (powLoop {X = typ X} {x = pt X} m) h))
    (λ h → local-prop {m = n}
      {A = fiber (powLoop {X = typ X} {x = pt X} m) h}) based

open PowerFibre public using (coprime-power-fibres-local)
