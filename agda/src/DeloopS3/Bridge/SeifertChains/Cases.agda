{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.SeifertChains.Cases where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import DeloopS3.Cert.Input.Model.Vocabulary using (ShortCase ; octa ; icosa)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.SeifertChains.Seifert

Kbase : ShortCase → ChainComplex ℓ-zero
Kbase octa = seifertK (pos 2) (pos 3) (pos 4)
Kbase icosa = seifertK (pos 2) (pos 3) (pos 5)

abstract
  Araw-octa-kernel : (v : fst ℤ⁶)
    → fst (Araw (pos 2) (pos 3) (pos 4)) v ≡ AbGroupStr.0g (snd vertex₁)
    → v ≡ AbGroupStr.0g (snd ℤ⁶)
  Araw-octa-kernel = Araw-kernel (pos 2) (pos 3) (pos 4)
    (positive-cancel 2) (positive-cancel 1)

  Araw-icosa-kernel : (v : fst ℤ⁶)
    → fst (Araw (pos 2) (pos 3) (pos 5)) v ≡ AbGroupStr.0g (snd vertex₁)
    → v ≡ AbGroupStr.0g (snd ℤ⁶)
  Araw-icosa-kernel = Araw-kernel (pos 2) (pos 3) (pos 5)
    (positive-cancel 2) (positive-cancel 0)

  base-H₂-zero : (c : ShortCase) → isContr (fst (homology 2 (Kbase c)))
  base-H₂-zero octa = Seifert.H₂-zero (pos 2) (pos 3) (pos 4)
    (positive-cancel 2) (positive-cancel 1)
  base-H₂-zero icosa = Seifert.H₂-zero (pos 2) (pos 3) (pos 5)
    (positive-cancel 2) (positive-cancel 0)

  source-223-H₂-zero : isContr (fst (homology 2 (seifertK (pos 2) (pos 2) (pos 3))))
  source-223-H₂-zero = Seifert.H₂-zero (pos 2) (pos 2) (pos 3)
    (positive-cancel 1) (positive-cancel 3)

  source-224-H₂-zero : isContr (fst (homology 2 (seifertK (pos 2) (pos 2) (pos 4))))
  source-224-H₂-zero = Seifert.H₂-zero (pos 2) (pos 2) (pos 4)
    (positive-cancel 1) (positive-cancel 3)
