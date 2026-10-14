{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Marked where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
import Cubical.Data.Int as Z
open import DeloopS3.Cert.Input.Model using (graphMark)
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Maps using (expand; treeRoute)
open import DeloopS3.Cert.Input.Graph.Total
open import DeloopS3.Cert.Input.Initial.Circle
open import DeloopS3.Cert.Input.Initial.Projection
open import DeloopS3.Cert.Input.LocalCharts.Actual using (boundary-fibre; boundary-fibre-base)
open import DeloopS3.Cert.Input.LocalCharts.Index
open import DeloopS3.Cert.Input.LocalCharts.Charts using (startSheet)
open import DeloopS3.Cert.Input.LocalCharts.Lift using (based-lift-unique)
open import DeloopS3.Cert.Input.LocalCharts.Family using (circle-connected)
open import DeloopS3.Cover.Cosets using (CosetFamily)
import DeloopS3.Cover.CircleOrbit as CO
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch

open import DeloopS3.Cert.Input.Initial.Actual

-- This is the whiskered circle square, with the actual first-sheet
-- fibre correction visible after the rooted tree route.
marked-boundary : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
  → liftToTotal c (expand c (R.wordCircle (gs c) (Ch.boundaryWord (bdAllAt c b)) u))
    ≡ overlapGraph c b u
marked-boundary c b u = cong (liftToTotal c) (expanded-boundary c b u)
  ∙ BoundaryLift.comparison c b u

abstract
  marked-boundary-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → marked-boundary c b R.0C
      ≡ cong (liftToTotal c) (treeRoute c (startSheet c b)) ∙ BoundaryLift.based c b
  marked-boundary-base c b i = cong (liftToTotal c) (expanded-boundary-base c b i)
    ∙ BoundaryLift.comparison-base c b i

