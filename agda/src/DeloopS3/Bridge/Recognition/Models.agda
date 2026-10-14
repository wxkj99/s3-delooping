{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Models where

open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.Recognition.Dimension
open import DeloopS3.Bridge.Recognition.Extension
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.Homotopy.Connected
open import DeloopS3.Local.Powers using (degSphere)

abstract
  moore3-finite≤ : (m : ℕ) → Finite≤ 4 (Moore m 2)
  moore3-finite≤ m = cofib-finite≤ (degSphere m 2) 3 3
    (sphere-finite≤ 3) (sphere-finite≤ 3)

  bottom-finite≤ : Finite≤ 3 BottomMoore
  bottom-finite≤ = cofib-finite≤ (degSphere 2 1) 2 2
    (sphere-finite≤ 2) (sphere-finite≤ 2)

moore3CW : ℕ → CW₀
moore3CW m = Moore m 2 , finite≤→isCW (moore3-finite≤ m)

bottomCW : CW₀
bottomCW = BottomMoore , finite≤→isCW bottom-finite≤

abstract
  moore3-connected : (m : ℕ) → isConnected 4 (Moore m 2)
  moore3-connected m = isConnectedCofib 2
    (isConnectedFunCancel' (degSphere m 2) (λ _ → tt) 3
      (isConnected→isConnectedFun 4 (sphereConnected 3))
      (isConnected→isConnectedFun 3 (isConnectedSubtr 3 1 (sphereConnected 3))))
