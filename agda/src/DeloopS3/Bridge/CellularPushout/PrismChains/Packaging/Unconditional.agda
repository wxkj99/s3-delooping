{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Unconditional where

open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Signature
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Final
import DeloopS3.Bridge.CellularPushout.PrismChains as RouteC

-- The all-degree finite-free triangular equivalence discharges the sole
-- parameter of the packaging theorem, for every strict cellular span.
triangular-input : TriangularInput
TriangularChains.q-is-equiv (triangular-input A B C f g) =
  RouteC.PrismChains.q-is-equiv A B C f g

-- Unconditional ComparisonInput, and the geometric LES of the ORIGINAL
-- arbitrary continuous finite CW span, with one propositional truncation.
open WithTriangularChains triangular-input public
  using (pushout-chains-input ; PushoutLES ; finite-pushoutLES-merely)
