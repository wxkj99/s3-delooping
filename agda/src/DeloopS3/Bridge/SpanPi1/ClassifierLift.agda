{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.ClassifierLift where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base using (inl)
open import Cubical.HITs.EilenbergMacLane1.Base
import DeloopS3.Cover.Cosets as Cosets
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Interpret.Short as Short
open Short using (ShortCase)

open import DeloopS3.Bridge.SpanPi1.TargetLoops public using (m₀)

a₀ : (c : ShortCase) → Model.A_G c
a₀ c = m₀ c , embase , refl

σ : (c : ShortCase) → Model.A_G c → EM₁ (Short.H c)
σ c = Cosets.coverToSubgroup (Short.j c) (Model.ρ-M c)

abstract
  classifier-loop-lift : (c : ShortCase)
    (l : m₀ c ≡ m₀ c) (d : fst (Short.H c))
    → cong (Model.ρ-M c) l
      ≡ emloop (fst (Cosets.hom (Short.j c)) d)
    → Σ[ L ∈ (a₀ c ≡ a₀ c) ]
        (cong fst L ≡ l) × (cong (σ c) L ≡ emloop d)
  classifier-loop-lift c l d eq =
    (λ i → l i , emloop d i , (λ j → eq (~ j) i)) , refl , refl
