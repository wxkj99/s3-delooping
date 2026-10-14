{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Circle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
import Cubical.HITs.S1.Base as S1
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Maps
open import DeloopS3.Cert.Input.Graph.Chart using (TreeChart; tree-chart)
open import DeloopS3.Cert.Input.Initial.Boundary
open import DeloopS3.Cert.Input.LocalCharts.Charts using (startSheet)
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch

-- This is the actual signed walk, closed by the reflected checker
-- endpoint, not an arbitrary lift with the same degree.
liftedBoundary : (c : ShortCase) → R.FaceIx (S₀ c) → R.C → LiftedGraph c
liftedBoundary c b u = R.circleRec (vertex (startSheet c b)) (boundaryLoop c b) (Circle.CToCircle u)

abstract
  collapse-boundary-on-S¹ : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : S1.S¹)
    → collapse c (R.circleRec (vertex (startSheet c b)) (boundaryLoop c b) u)
      ≡ R.circleRec R.root (R.roseWord (gs c) (Ch.boundaryWord (bdAllAt c b))) u
  collapse-boundary-on-S¹ c b S1.base = refl
  collapse-boundary-on-S¹ c b (S1.loop i) j = collapse-boundaryLoop c b j i

  collapse-boundary : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
    → collapse c (liftedBoundary c b u)
      ≡ R.wordCircle (gs c) (Ch.boundaryWord (bdAllAt c b)) u
  collapse-boundary c b u = collapse-boundary-on-S¹ c b (Circle.CToCircle u)

  collapse-boundary-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → collapse-boundary c b R.0C ≡ refl
  collapse-boundary-base c b = refl

-- Reverse only after proving the constant-based collapse homotopy.
-- The resulting path starts at the root and ends at the checked sheet.
expanded-boundary : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
  → expand c (R.wordCircle (gs c) (Ch.boundaryWord (bdAllAt c b)) u)
    ≡ liftedBoundary c b u
expanded-boundary c b u = cong (expand c) (sym (collapse-boundary c b u))
  ∙ TreeChart.counit (tree-chart c) (liftedBoundary c b u)

abstract
  expanded-boundary-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → expanded-boundary c b R.0C ≡ treeRoute c (startSheet c b)
  expanded-boundary-base c b =
    cong (λ p → cong (expand c) (sym p) ∙ TreeChart.counit (tree-chart c) (vertex (startSheet c b)))
      (collapse-boundary-base c b)
    ∙ sym (lUnit (TreeChart.counit (tree-chart c) (vertex (startSheet c b))))
    ∙ TreeChart.counit-vertex (tree-chart c) (startSheet c b)
