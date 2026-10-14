{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Assembly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
open import DeloopS3.Move.CancelMinimalCore using (EquivOver)
open import DeloopS3.Cert.Input.Model public using
  (InitialCharts; ShortCase; S₀; M_G; Q; A_G; FlatSpan)
open import DeloopS3.Cert.Input.Model using
  (initialChartSpan; module Flat; flatten-total; flatten-over)
import DeloopS3.Cert.Input.LocalCharts as Local
import DeloopS3.Cert.Input.Initial.Left as Left
import DeloopS3.Cert.Interpret.Realization as R

-- All fields refer to Ch.initialState (certOf c), not a generated
-- state-0. No primitive cancellation program is interpreted here.
initial-charts : (c : ShortCase) → InitialCharts c
InitialCharts.leftChart (initial-charts c) = Left.leftChart c
InitialCharts.overlapChart (initial-charts c) = Local.LocalCharts.overlapChart (Local.local-charts c)
InitialCharts.rightChart (initial-charts c) = Local.LocalCharts.rightChart (Local.local-charts c)
InitialCharts.leftSquare (initial-charts c) = Left.leftSquare c
InitialCharts.rightSquare (initial-charts c) = Local.LocalCharts.rightSquare (Local.local-charts c)

initial-span : (c : ShortCase) → R.SpanEquiv (R.diagram (S₀ c)) (FlatSpan c)
initial-span c = initialChartSpan c (initial-charts c)

