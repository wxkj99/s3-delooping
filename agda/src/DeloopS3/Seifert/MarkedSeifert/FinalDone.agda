{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The Seifert/bundle equivalence and π₂ vanishing for e ≠ 0, using Finish's
-- total equivalence and full torus-boundary path.
module DeloopS3.Seifert.MarkedSeifert.FinalDone where

open import DeloopS3.Seifert.MarkedSeifert.Final public
  using (M22e; pt; module Bundle)
import DeloopS3.Seifert.MarkedSeifert.Final as Final
open import DeloopS3.Seifert.MarkedSeifert.DescentChart.Finish public
  using (descentChart)

private
  module Complete = Final.FromDescentChart descentChart

-- Re-export, rather than repackage, so that the equivalence appearing in
-- p22 and projectionPath is exactly the one exported as M22e≃Mₑ.
open Complete public
  using (M22e≃Mₑ; p22; projectionPath; fibreComparison; circleFibres;
         capFibre; pi₂-M22e-zero)
