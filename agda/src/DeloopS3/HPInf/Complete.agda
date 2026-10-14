{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.Complete where

-- Unconditional maximal torus for the original concrete S³ delooping.
-- This does not assert an equivalence to an independently defined HP∞ model.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber; _≃_)
open import Cubical.Foundations.Pointed using (Pointed; typ; pt; _→∙_; _≃∙_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Loopspace using (Ω)
import DeloopS3.HPInf.Inputs as Inputs
import DeloopS3.HPInf.CommonSquare as Square
open import DeloopS3.HPInf.RelativeFracture using (common-square-cartesian)
open import DeloopS3.HPInf.TorusFromCorner using
  (K₂∙; MaximalTorus; module FromCartesianCorner)

B : Pointed ℓ-zero
B = Inputs.B

module Torus = FromCartesianCorner B Square.j Square.j-point
  Square.ET Square.alpha Square.pT Square.H common-square-cartesian
  (Square.ET-contr Inputs.homology)

t : K₂∙ →∙ B
t = Torus.t

t-fiber : fiber (fst t) (pt B) ≃ S₊ 2
t-fiber = Torus.t-fiber

maximal-torus : MaximalTorus B
maximal-torus = t , t-fiber

B-connected : isConnected 2 (typ B)
B-connected = Inputs.B-connected

ΩB≃S³ : Ω B ≃∙ (S₊ 3 , north)
ΩB≃S³ = Inputs.ΩB≃S³

S³-delooping-with-maximal-torus : Σ[ X ∈ Pointed ℓ-zero ]
  (isConnected 2 (typ X) × ((Ω X ≃∙ (S₊ 3 , north)) × MaximalTorus X))
S³-delooping-with-maximal-torus = B , B-connected , ΩB≃S³ , maximal-torus
