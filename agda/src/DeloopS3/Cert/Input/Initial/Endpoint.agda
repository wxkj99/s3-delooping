{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Endpoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import DeloopS3.Move.CancelMinimalCore using (EquivOver)
open import DeloopS3.Cert.Input.Model using
  (ShortCase; S₀; M_G; Q; A_G; module Flat; flatten-over)
open import DeloopS3.Cert.Input.Initial.Assembly
open import DeloopS3.Cert.Input.Initial.SpanProjection using (module Prescribed)
import DeloopS3.Cert.Interpret.Realization as R

-- The constructor map is prescribed by the chart projections and the
-- left-square / original push / inverse right-square seam. The generic
-- proof is sealed before specializing to the concrete finite charts.
module Assembled (c : ShortCase) = Prescribed (initial-span c) (Flat.projection c)

-- Model.flatten-over is FamilyFlattening.over. Its first
-- field is the prescribed flattening equivalence; reuse that SAME
-- opaque field in the map and its projection proof.
cover-initial : (c : ShortCase) → R.T (S₀ c) ≃ A_G c
cover-initial c = compEquiv (R.SpanMap.spanEquiv (initial-span c)) (flatten-over c .fst)

initialProjection : (c : ShortCase) → R.T (S₀ c) → M_G c
initialProjection c = Assembled.projection c

abstract
  cover-initial-projection : (c : ShortCase) (x : R.T (S₀ c))
    → initialProjection c x ≡ fst (equivFun (cover-initial c) x)
  cover-initial-projection c x = Assembled.projection-agrees c x
    ∙ flatten-over c .snd (equivFun (R.SpanMap.spanEquiv (initial-span c)) x)

-- Keep the equivalence component literal while sealing its proof.
cover-initial-over : (c : ShortCase)
  → EquivOver (initialProjection c) (fst {B = Q c})
cover-initial-over c = cover-initial c , cover-initial-projection c
