{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Fracture where

-- The canonical arithmetic fracture equivalence.
-- 2-connectedness is essential: the arithmetic heart uses Route B over
-- the simply connected loop space.  The canonical map needs no basepoint.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; isPropIsEquiv)
open import Cubical.Foundations.HLevels using (isProp→isOfHLevelSuc)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Connected using
  (isConnected ; isConnectedSubtr ; isConnectedPath)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as Tr
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout ; bezout-3-10)
open import DeloopS3.Local.Fracture.Fracture.Maps public
  using (PB ; ι_m ; ι_n ; ι_m-β ; ι_n-β ; fracture-unit)
open import DeloopS3.Local.Fracture.Fracture.Assembly using (module Assembly)

abstract
  arithmetic-fracture-2-connected : (m n : ℕ) (A : Type)
    → isConnected 4 A → Bezout m n → isEquiv (fracture-unit m n A)
  arithmetic-fracture-2-connected m n A conn bez =
    PT.rec (isPropIsEquiv (fracture-unit m n A)) pointed inhabited
    where
    pointed : A → isEquiv (fracture-unit m n A)
    pointed a = Assembly.pointed-fracture m n A
      (isConnectedSubtr {A = A} 3 1 conn) a
      (isConnectedPath 3 {A = A} conn a a) bez

    inhabited : PT.∥ A ∥₁
    inhabited = Tr.rec (isProp→isOfHLevelSuc 3 PT.squash₁) PT.∣_∣₁ (fst conn)

  arithmetic-fracture-S³ : isEquiv (fracture-unit 3 10 (S₊ 3))
  arithmetic-fracture-S³ = arithmetic-fracture-2-connected 3 10 (S₊ 3)
    (sphereConnected 3) bezout-3-10
