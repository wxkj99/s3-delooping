{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Map

-- No homology comparison or continuous-map square is an input here.
-- The forward map is the triangular map, including the identity
-- on augmentation and the actual source/vertex cellular coefficients.
record TriangularChains (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) : Type where
  module PM = PrismMap A B C f g
  field
    q-is-equiv : isChainEquiv PM.q-chain
  q-equivalence : PM.CP.DMC ≃Chain PM.actual
  q-equivalence = PM.q-chain , q-is-equiv
  pushout-chains : PM.actual ≃Chain PM.CP.DMC
  pushout-chains = invChainEquiv q-equivalence
  q-vertexB : compChainMap PM.CP.inclB (fst q-equivalence) ≡ PM.vertexB-chain
  q-vertexB = PM.q-vertexB
  q-vertexC : compChainMap PM.CP.inclC (fst q-equivalence) ≡ PM.vertexC-chain
  q-vertexC = PM.q-vertexC
