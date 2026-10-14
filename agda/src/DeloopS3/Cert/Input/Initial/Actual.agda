{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Actual where

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

-- The graph component of the literal overlap chart. The opaque fibre
-- is the one already supplied by LocalCharts, not a chosen new lift.
overlapGraph : (c : ShortCase) → R.FaceIx (S₀ c) → R.C → GraphTotal c
overlapGraph c b u = R.wordCircle twoGenerators (Ch.kindWord (kindAt c b))
  (R.mulC (Z.pos (suc (ellPred c (kindAt c b) (localAt c b)))) u) ,
  boundary-fibre c (kindAt c b) (localAt c b) u

abstract
  overlapGraph-projection : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
    → fst (overlapGraph c b u) ≡ boundaryProjection c b u
  overlapGraph-projection c b u i = R.wordCircle twoGenerators
    (Ch.kindWord (kind-index (face-data c b) i))
    (R.mulC (Z.pos (length-index (face-data c b) i)) u)

  overlapGraph-projection-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → overlapGraph-projection c b R.0C ≡ refl
  overlapGraph-projection-base c b = refl

module BoundaryLift (c : ShortCase) (b : R.FaceIx (S₀ c)) where
  f g : R.C → GraphTotal c
  f u = liftToTotal c (liftedBoundary c b u)
  g = overlapGraph c b

  h : (u : R.C) → fst (f u) ≡ fst (g u)
  h u = liftToTotal-over c (liftedBoundary c b u)
    ∙ (liftedBoundary-projection c b u ∙ sym (overlapGraph-projection c b u))

  based : f R.0C ≡ g R.0C
  based i = R.root , boundary-fibre-base c (kindAt c b) (localAt c b) (~ i)

  abstract
    h-base : h R.0C ≡ refl
    h-base = cong (refl ∙_) (cong₂ _∙_ (liftedBoundary-projection-base c b)
      (cong sym (overlapGraph-projection-base c b)))
      ∙ sym (lUnit (refl ∙ refl)) ∙ sym (lUnit refl)

    based-over : cong fst based ≡ h R.0C
    based-over = sym h-base

    lifted : Σ[ H ∈ ((u : R.C) → f u ≡ g u) ] ((u : R.C) → cong fst (H u) ≡ h u)
    lifted = based-lift-unique {B = Γ} {X = R.C} (GraphFamily c)
      (λ x → CosetFamily (j c) (graphMark c x) .snd)
      R.0C circle-connected f g h based based-over

  comparison : (u : R.C) → f u ≡ g u
  comparison = lifted .fst

  comparison-over : (u : R.C) → cong fst (comparison u) ≡ h u
  comparison-over = lifted .snd

  abstract
    comparison-base : comparison R.0C ≡ based
    comparison-base = CO.cover-path-ext (λ x → CosetFamily (j c) (graphMark c x))
      (comparison R.0C) based (comparison-over R.0C ∙ sym based-over)

