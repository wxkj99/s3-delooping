{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Assembly.Complete where

-- A connected pointed delooping of S³, with all geometric and homological
-- inputs supplied by the cover-degree and profile constructions.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed; typ; _≃∙_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Loopspace using (Ω)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.DegreeSpan.CoverDegreeFromH2 using
  (cover-degree-from-H2)
import DeloopS3.Bridge.DegreeSpan.LeftComparisons as LeftComparisons
open import DeloopS3.Bridge.Profile.FromCoverDegree using
  (CoverDegreeInput; Deloop-from-cover-degree)

cover-degree-input : PT.∥ CoverDegreeInput ∥₁
cover-degree-input = cover-degree-from-H2
  (λ c → PT.∣ LeftComparisons.comparisons c ∣₁)

Deloop-S3 : Σ[ B ∈ Pointed ℓ-zero ]
  (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
Deloop-S3 = Deloop-from-cover-degree cover-degree-input
