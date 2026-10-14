{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCoordinatePair where

-- Pair assembly is elaborated on neutral integer coordinates, before
-- substitution of the large actual target homology action.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sigma using (ΣPathP)
open import DeloopS3.Cert.Check using (Kind ; kindWord)
open import DeloopS3.Bridge.CoverChains.Generators using (targetTorus)
import DeloopS3.Bridge.CoverChains.Words as Words
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Bridge.DegreeSpan.LeftCoordinateAlgebra as Algebra

abstract
  base-column : (r : Fin 2 → ℤ) (k : Kind) (t : ℤ)
    → r fzero ≡ Words.wordExponent 1 (kindWord k) Z.· t
    → r (fsuc fzero) ≡ Words.wordExponent 2 (kindWord k) Z.· t
    → (r fzero , r (fsuc fzero)) ≡ fst Base.D (targetTorus k t)
  base-column r k t a b = ΣPathP (a , b) ∙ Algebra.base-word-column k t
