{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Actual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Data.Sigma
open import Cubical.HITs.EilenbergMacLane1.Base using (EM₁; embase; emloop; emloop-comp)
open import DeloopS3.Cert.Input.Model
open import DeloopS3.Cert.Input.Sheets
open import DeloopS3.Cert.Input.Orbits using (short-orbits)
open import DeloopS3.Cert.Input.LocalCharts.Family
open import DeloopS3.Cover.Cosets using (CosetFamily)
import DeloopS3.Cover.CircleOrbit as CO
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R

CoreFamily BoundaryFamily : (c : ShortCase) → Ch.Kind → R.C → Type₀
CoreFamily c k u = CosetFamily (j c) (coreMark c k u) .fst
BoundaryFamily c k u = CosetFamily (j c) (boundaryMark c k u) .fst

sheet : (c : ShortCase) → Sh c → CosetFamily (j c) embase .fst
sheet c = equivFun (SheetData.e (sheet-data c))

abstract
  generator-square : (c : ShortCase) (k : Ch.Kind) (x : Sh c)
    → subst (λ b → CosetFamily (j c) b .fst) (emloop (genElement c k)) (sheet c x)
      ≡ sheet c (CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst x)
  generator-square c Ch.A x = SheetData.square (sheet-data c) x a+
  generator-square c Ch.B x = SheetData.square (sheet-data c) x b+
  generator-square c Ch.C x =
    cong (λ p → subst F p (sheet c x))
      (cong emloop (gen-c-inverses c)
       ∙ emloop-comp (Δ c) (letterElement c b-) (letterElement c a-))
    ∙ substComposite F (emloop (letterElement c b-)) (emloop (letterElement c a-)) (sheet c x)
    ∙ cong (subst F (emloop (letterElement c a-))) (SheetData.square (sheet-data c) x b-)
    ∙ SheetData.square (sheet-data c) (actFin (certOf c) (rawChecks c) b- x) a-
    where
    F : EM₁ (Δ c) → Type₀
    F b = CosetFamily (j c) b .fst

  core-square : (c : ShortCase) (k : Ch.Kind) (x : Sh c)
    → subst (CoreFamily c k) Circle.hC (sheet c x)
      ≡ sheet c (CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst x)
  core-square c k x = cong (λ p → subst (λ b → CosetFamily (j c) b .fst) p (sheet c x))
    (coreMark-positive c k) ∙ generator-square c k x

  boundary-square : (c : ShortCase) (k : Ch.Kind) (x : Sh c)
    → subst (BoundaryFamily c k) Circle.hC (sheet c x)
      ≡ sheet c (CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst x)
  boundary-square c k x = cong (λ p → subst (λ b → CosetFamily (j c) b .fst) p (sheet c x))
    (boundaryMark-loop c k) ∙ generator-square c k x

module Core (c : ShortCase) (k : Ch.Kind) = Comparison
  (localPermutation (certOf c) (rawChecks c) k) (short-orbits c k)
  (CoreFamily c k) (SheetData.e (sheet-data c)) (core-square c k)
module Boundary (c : ShortCase) (k : Ch.Kind) = Comparison
  (localPermutation (certOf c) (rawChecks c) k) (short-orbits c k)
  (BoundaryFamily c k) (SheetData.e (sheet-data c)) (boundary-square c k)

-- The overlap family is literally independent of the fibre coordinate.
-- In particular this is not a second, nontrivial circle action.
abstract
  fibre-action-trivial : (c : ShortCase) (k : Ch.Kind) (u : R.C)
    (q : BoundaryFamily c k u)
    → subst (λ t → BoundaryFamily c k u) Circle.hC q ≡ q
  fibre-action-trivial c k u q = transportRefl q

open import Cubical.Data.Nat using (suc)
import Cubical.Data.Int as Z

-- Opaque fibre coordinates: conversion in later Sigma-path proofs must
-- not re-expand the cyclic action, orbit comparison, or finite groups.
-- Their projections remain literal positive multiplication maps.
abstract
  core-fibre : (c : ShortCase) (k : Ch.Kind) (b : Bd c k) (u : R.C)
    → CoreFamily c k (R.mulC (Z.pos (suc (ellPred c k b))) u)
  core-fibre c k b u = Core.positive c k (b , u) .snd

  boundary-fibre : (c : ShortCase) (k : Ch.Kind) (b : Bd c k) (u : R.C)
    → BoundaryFamily c k (R.mulC (Z.pos (suc (ellPred c k b))) u)
  boundary-fibre c k b u = Boundary.positive c k (b , u) .snd

  core-fibre-base : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → core-fibre c k b R.0C ≡ sheet c (startOf c k b)
  core-fibre-base = Core.positive-base-fibre

  boundary-fibre-base : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → boundary-fibre c k b R.0C ≡ sheet c (startOf c k b)
  boundary-fibre-base = Boundary.positive-base-fibre

core-positive : (c : ShortCase) (k : Ch.Kind) → Bd c k × R.C → Σ R.C (CoreFamily c k)
core-positive c k (b , u) = R.mulC (Z.pos (suc (ellPred c k b))) u , core-fibre c k b u

boundary-positive : (c : ShortCase) (k : Ch.Kind) → Bd c k × R.C → Σ R.C (BoundaryFamily c k)
boundary-positive c k (b , u) = R.mulC (Z.pos (suc (ellPred c k b))) u , boundary-fibre c k b u

abstract
  core-positive-isEquiv : (c : ShortCase) (k : Ch.Kind) → isEquiv (core-positive c k)
  core-positive-isEquiv = Core.positive-isEquiv

  boundary-positive-isEquiv : (c : ShortCase) (k : Ch.Kind) → isEquiv (boundary-positive c k)
  boundary-positive-isEquiv = Boundary.positive-isEquiv

core-circles : (c : ShortCase) (k : Ch.Kind) → (Bd c k × R.C) ≃ Σ R.C (CoreFamily c k)
core-circles c k = core-positive c k , core-positive-isEquiv c k

boundary-circles : (c : ShortCase) (k : Ch.Kind) → (Bd c k × R.C) ≃ Σ R.C (BoundaryFamily c k)
boundary-circles c k = boundary-positive c k , boundary-positive-isEquiv c k
