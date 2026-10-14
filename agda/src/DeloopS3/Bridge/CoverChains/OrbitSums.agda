{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.OrbitSums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
import Cubical.Data.SumFin as SF
open import Cubical.Data.FinSet.Base using (FinSet; card)
open import Cubical.Data.FinSet.Properties using (isFinSetFin)
open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)
import Cubical.Data.FinSet.Cardinality as Cardinal
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Cert.Input.Model.Vocabulary public
open import DeloopS3.Cert.Input.Orbits using (cycleCoordinates)
open import DeloopS3.Cert.Check public using (Kind; A; B; C)
import DeloopS3.Cert.Check as Ch

-- Cardinal's finite sum is defined by the cardinal of the dependent sum.
-- Thus this counts orbit POSITIONS, not just orbit representatives.
sumBd : (c : ShortCase) (k : Kind) → (Bd c k → ℕ) → ℕ
sumBd c k = Cardinal.sum (Bd c k , isFinSetFin)

N : ShortCase → ℕ
N c = Ch.index (certOf c)

abstract
  sum-under-bijection : {X Y : FinSet ℓ-zero} (e : fst X ≃ fst Y)
    (f : fst Y → ℕ)
    → Cardinal.sum X (λ x → f (equivFun e x)) ≡ Cardinal.sum Y f
  sum-under-bijection {X} {Y} e f = Cardinal.cardEquiv
    (_ , isFinSetΣ X (λ x → SF.Fin (f (equivFun e x)) , isFinSetFin))
    (_ , isFinSetΣ Y (λ y → SF.Fin (f y) , isFinSetFin))
    PT.∣ Σ-cong-equiv-fst e ∣₁

  orbit-length-sum : (c : ShortCase) (k : Kind)
    → sumBd c k (λ b → suc (ellPred c k b)) ≡ N c
  orbit-length-sum c k = Cardinal.cardEquiv
    (_ , isFinSetΣ (Bd c k , isFinSetFin)
      (λ b → SF.Fin (suc (ellPred c k b)) , isFinSetFin))
    (Sh c , isFinSetFin)
    PT.∣ compEquiv
      (Σ-cong-equiv-snd (λ b → SF.SumFin≃Fin (suc (ellPred c k b))))
      (cycleCoordinates c k) ∣₁
