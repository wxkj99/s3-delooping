{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains where

open import DeloopS3.Bridge.CellularPushout.PrismChains.Map public
open import DeloopS3.Bridge.CellularPushout.PrismChains.Triangular public
open import DeloopS3.Bridge.CellularPushout.PrismChains.Comparison public
open import DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFree public
open import DeloopS3.Bridge.CellularPushout.PrismChains.Actual public

-- All-degree, support-free triangular comparison whose first two
-- coordinates may mix prism terms.
open import Cubical.Foundations.Prelude using (ℓ-zero)
open import Cubical.CW.Base using (CWskel)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)

module PrismChains (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  open Comparison A B C f g public
  open Complete finite-free-direct-finite public
  open ActualVertices A B C f g public
    using (vertexB-homology-actual ; vertexC-homology-actual ; vertexB-Hβ ; vertexC-Hβ)
