{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Final where

open import Cubical.Foundations.Prelude
open import Cubical.CW.Base using (CWskel)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Signature
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Strict
open import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Descent
open import DeloopS3.Bridge.DMCExactness.Conditional

-- A triangular chain equivalence for each strict cellular span supplies
-- the comparison for arbitrary continuous finite CW spans.
TriangularInput : Type₁
TriangularInput = (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C))
  → TriangularChains A B C f g

module WithTriangularChains (triangular : TriangularInput) where
  private
    strict-input : StrictSpanComparison
    strict-input A B C f g = Strict.strict-comparison A B C f g (triangular A B C f g)
    module Descend = FromStrict strict-input

  abstract
    pushout-chains-input : ComparisonInput
    pushout-chains-input = Descend.comparison-input

  -- One outer propositional truncation contains all skeletal choices and
  -- both cellular approximations, exactly as in Conditional.agda.
  open Conditional pushout-chains-input public using (PushoutLES ; finite-pushoutLES-merely)
