{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.SeifertChains.Arithmetic where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver

-- Solve polynomial identities before instantiating the integer operations.
module Polynomial {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  abstract
    difference-add : (x y z w : fst R)
      → (x + y) - (z + w) ≡ (x - z) + (y - w)
    difference-add _ _ _ _ = solve! R

    sum3-add : (a b c d e f : fst R)
      → (a + d) + ((b + e) + (c + f)) ≡ (a + (b + c)) + (d + (e + f))
    sum3-add _ _ _ _ _ _ = solve! R

    row-add : (p q u v x y : fst R)
      → - (p · (u + v) + q · (x + y))
        ≡ (- (p · u + q · x)) + (- (p · v + q · y))
    row-add _ _ _ _ _ _ = solve! R

    unit-row-add : (p u v x y : fst R)
      → - ((u + v) + p · (x + y)) ≡ (- (u + p · x)) + (- (v + p · y))
    unit-row-add _ _ _ _ _ = solve! R

    solve-sum3 : (x y z : fst R)
      → z ≡ - (x + y) + (x + (y + z))
    solve-sum3 _ _ _ = solve! R

    solve-unit : (z p x : fst R)
      → z ≡ - (p · x) - (- (z + p · x))
    solve-unit _ _ _ = solve! R

    residual-one : (p q x y : fst R)
      → - ((- (p · x)) + q · y) ≡ p · x - q · y
    residual-one _ _ _ _ = solve! R

    residual-two : (p r x y : fst R)
      → - ((1r - r) · (- (p · x)) + r · (- (x + y)))
        ≡ (p + r - p · r) · x + r · y
    residual-two _ _ _ _ = solve! R

    eliminate : (p q r x y : fst R)
      → (p · q + p · r + q · r - p · q · r) · x
        ≡ r · (p · x - q · y) + q · ((p + r - p · r) · x + r · y)
    eliminate _ _ _ _ _ = solve! R

    zero-first : (p q y : fst R)
      → p · 0r - q · y ≡ - (q · y)
    zero-first _ _ _ = solve! R

open Polynomial ℤCommRing public
