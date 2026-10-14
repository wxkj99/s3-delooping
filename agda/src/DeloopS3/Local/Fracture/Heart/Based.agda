{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Heart.Based where

-- Locality of the based fibre: invert the power on ΩF, then use
-- connectedness of F.  F itself is not assumed to be a loop space.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Loopspace using (Ω)
open import Cubical.Homotopy.Connected using (isConnectedSubtr)
open import DeloopS3.Local.Base using (Local ; L ; η ; powLoop)
open import DeloopS3.Local.RouteB2 using (L∙ ; η∙ ; L-preserves-SC)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using
  (Conn ; SC ; connected-fiber-SC-base ; connected-based-powers→local)
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout)
open import DeloopS3.Local.Fracture.Arithmetic.LoopFiber using (module LoopedFiber)
open import DeloopS3.Local.Fracture.Heart.PowerSquare using (module PowerSquare)

module UnitFibre (m n : ℕ) (X : Pointed ℓ-zero)
  (scX : SC (typ X)) (scH : SC (typ (Ω X))) (bez : Bezout m n) where

  private
    module LF = LoopedFiber X (L∙ n X) (η∙ n X)

  abstract
    localized-SC : SC (L n (typ X))
    localized-SC = L-preserves-SC n {X = typ X} scX

    localized-connected : Conn (L n (typ X))
    localized-connected = isConnectedSubtr {A = L n (typ X)} 2 1 localized-SC

    fibre-connected : Conn (fiber (η {n} {typ X}) (η {n} {typ X} (pt X)))
    fibre-connected = connected-fiber-SC-base {E = typ X} {B = L n (typ X)}
      (η {n} {typ X}) (isConnectedSubtr {A = typ X} 2 1 scX)
      localized-SC (η {n} {typ X} (pt X))

    fibre-loop-power : isEquiv (powLoop {X = typ LF.W} {x = pt LF.W} m)
    fibre-loop-power = LF.cartesian-power→loop-power m
      (PowerSquare.pointed-squares m n X scX scH bez (LF.powerNaturality m))

    based-local : Local m (fiber (η {n} {typ X}) (η {n} {typ X} (pt X)))
    based-local = connected-based-powers→local m LF.W fibre-connected fibre-loop-power
