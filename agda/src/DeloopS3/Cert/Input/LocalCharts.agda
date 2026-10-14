{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts where

open import DeloopS3.Cert.Input.LocalCharts.Lift public
open import DeloopS3.Cert.Input.LocalCharts.Family public
open import DeloopS3.Cert.Input.LocalCharts.Actual public
open import DeloopS3.Cert.Input.LocalCharts.Index public
open import DeloopS3.Cert.Input.LocalCharts.Row public
open import DeloopS3.Cert.Input.LocalCharts.Charts public
  hiding (overlapChart; overlap-projection; right-projection; overlap-base; right-base)
open import DeloopS3.Cert.Input.LocalCharts.Square public hiding (rightSquare)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
import Cubical.Data.Int as Z
open import DeloopS3.Cert.Input.Model using (ShortCase; S₀; FlatSpan; bdAllAt)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.LocalCharts.Charts as Charts
import DeloopS3.Cert.Input.LocalCharts.Square as Square

-- Local covering charts and their squares over the family-flattened span.
record LocalCharts (c : ShortCase) : Type₁ where
  field
    overlapChart : R.O (S₀ c) ≃ R.Span.O (FlatSpan c)
    rightChart : R.R (S₀ c) ≃ R.Span.R (FlatSpan c)
    overlap-projection : (b : R.FaceIx (S₀ c)) (u t : R.C)
      → fst (equivFun overlapChart (b , u , t))
        ≡ (Ch.kind (bdAllAt c b) ,
            R.mulC (Z.pos (Ch.orbitLength (bdAllAt c b))) u , t)
    right-projection : (b : R.FaceIx (S₀ c)) (u : R.C)
      → fst (equivFun rightChart (b , u))
        ≡ (Ch.kind (bdAllAt c b) ,
            R.mulC (Z.pos (Ch.orbitLength (bdAllAt c b))) u)
    overlap-base : (b : R.FaceIx (S₀ c))
      → equivFun overlapChart (b , R.0C , R.0C) ≡ boundaryOrigin c b
    right-base : (b : R.FaceIx (S₀ c))
      → equivFun rightChart (b , R.0C) ≡ coreOrigin c b
    rightSquare : (z : R.O (S₀ c))
      → equivFun rightChart (R.right (S₀ c) z)
        ≡ R.Span.right (FlatSpan c) (equivFun overlapChart z)

local-charts : (c : ShortCase) → LocalCharts c
LocalCharts.overlapChart (local-charts c) = Charts.overlapChart c
LocalCharts.rightChart (local-charts c) = Charts.coreChart c
LocalCharts.overlap-projection (local-charts c) = Charts.overlap-projection c
LocalCharts.right-projection (local-charts c) = Charts.right-projection c
LocalCharts.overlap-base (local-charts c) = Charts.overlap-base c
LocalCharts.right-base (local-charts c) = Charts.right-base c
LocalCharts.rightSquare (local-charts c) = Square.rightSquare c
