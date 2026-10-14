{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.Inputs where

-- Unconditional inputs for the same concrete localized pullback as Final.
-- Eliminate finite choices only through the existing contraction interface.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed; typ; _≃∙_)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Loopspace using (Ω)
open import DeloopS3.Local.Base using (L)
open import DeloopS3.Local.RouteB2 using (SC)
import DeloopS3.Assembly.Complete as Complete
import DeloopS3.Assembly.ConnectivityGlue as Connectivity
import DeloopS3.Assembly.DefB as DefB
import DeloopS3.Assembly.Final as Final
import DeloopS3.Assembly.Final.Geometry as Geometry
import DeloopS3.Assembly.SimpleFromPi1 as Simple
import DeloopS3.Bridge.Profile.Assembly as Profile
import DeloopS3.Bridge.Profile.FromCoverDegree as Degree

abstract
  homology : Final.HomologyProfileInput
  homology = Profile.profileFacts→HomologyProfileInput
    (Degree.coverDegree→profileFacts Complete.cover-degree-input)

  fibres : Final.FibreInput
  fibres = Connectivity.fibreInput-from-simple Simple.simpleInput

module Assembly = Final.Assemble homology fibres

B : Pointed ℓ-zero
B = DefB.B-def (Geometry.Q Geometry.octa) (Geometry.Q Geometry.icosa)
  Geometry.T (Geometry.u Geometry.octa) (Geometry.u Geometry.icosa)

abstract
  base-SC : (c : Geometry.ShortCase) → SC (Geometry.P c)
  base-SC = Assembly.base-SC

  star-base-SC : SC Geometry.P*
  star-base-SC = Assembly.star-base-SC

  total-local-contractible : (c : Geometry.ShortCase)
    → isContr (L (Geometry.m c) (Geometry.E c))
  total-local-contractible = Final.contrG homology

  star-total-local-contractible : isContr (L 30 Geometry.E*)
  star-total-local-contractible = Final.contrStar homology

  B-connected : isConnected 2 (typ B)
  B-connected = DefB.B-connected
    (Geometry.Q Geometry.octa) (Geometry.Q Geometry.icosa) Geometry.T
    (Geometry.u Geometry.octa) (Geometry.u Geometry.icosa)
    (DefB.NaturalLoopData.Q1-connected Assembly.naturalLoopData)
    (DefB.NaturalLoopData.Q2-connected Assembly.naturalLoopData)
    (DefB.NaturalLoopData.T-simply-connected Assembly.naturalLoopData)

  ΩB≃S³ : Ω B ≃∙ (S₊ 3 , north)
  ΩB≃S³ = DefB.ΩB≃S³
    (Geometry.Q Geometry.octa) (Geometry.Q Geometry.icosa) Geometry.T
    (Geometry.u Geometry.octa) (Geometry.u Geometry.icosa)
    Assembly.naturalLoopData
