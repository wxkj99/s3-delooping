{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.Degree where

-- Degree calibration for the actual sphere maps used by Local.EO/EI.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; _+_ ; pos+)
open import Cubical.HITs.S1.Base using (loop ; winding ; winding-hom)
open import Cubical.HITs.Sn.Degree using (degree ; degreeSusp)
open import DeloopS3.Local.Base using (powLoop ; deg₁)
open import DeloopS3.Local.Powers using (degSphere)

private
  winding-powLoop : (m : ℕ) → winding (powLoop m loop) ≡ pos m
  winding-powLoop zero = refl
  winding-powLoop (suc m) = winding-hom loop (powLoop m loop)
    ∙ cong (pos 1 +_) (winding-powLoop m) ∙ sym (pos+ 1 m)

degree-deg₁ : (m : ℕ) → degree 1 (deg₁ m) ≡ pos m
degree-deg₁ = winding-powLoop

degree-degSphere-S² : (m : ℕ) → degree 2 (degSphere m 1) ≡ pos m
degree-degSphere-S² m = sym (degreeSusp 1 (deg₁ m)) ∙ degree-deg₁ m

degree-degSphere-S³ : (m : ℕ) → degree 3 (degSphere m 2) ≡ pos m
degree-degSphere-S³ m = sym (degreeSusp 2 (degSphere m 1)) ∙ degree-degSphere-S² m
