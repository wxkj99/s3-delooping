{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Interpret.Realized where

-- A realized move carries a total-space equivalence and its inverse cocone.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
import DeloopS3.Cert.Check as Ch
open import DeloopS3.Cert.Interpret.Syntax using (WellFormed)
open import DeloopS3.Cert.Interpret.Realization using (T; L; R; O; left; right)
open import DeloopS3.Move.CancelLoopCell using (module PushoutUP)

record RealizedStep (n : ℕ) (S S′ : Ch.State) : Type where
  field
    next-wf : WellFormed n S′
    total : T S ≃ T S′
    backLeft : L S′ → T S
    backRight : R S′ → T S
    backSeam : (a : O S′) → backLeft (left S′ a) ≡ backRight (right S′ a)
    back-rec : invEq total ≡ PushoutUP.extend (left S′) (right S′) (T S)
      (backLeft , backRight , backSeam)
