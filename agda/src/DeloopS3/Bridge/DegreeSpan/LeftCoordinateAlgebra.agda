{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCoordinateAlgebra where

-- Small scalar calculations, kept independent of the actual homology
-- endpoints so that the final adapters only compose the equations.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Sigma using (ΣPathP)
open import DeloopS3.Bridge.CoverChains.Incidence using
  (Bdy ; Tori ; Dhat ; rawIncidence ; orbit)
open import DeloopS3.Bridge.CoverChains.OrbitSums using
  (ShortCase ; Sh ; A ; B ; C ; Kind)
open import DeloopS3.Cert.Input.Graph.Base using (Generator ; ga ; gb ; nextSheet)
open import DeloopS3.Cert.Input.Graph.Maps using (Petal ; nonTree)
open import DeloopS3.Bridge.CoverChains.Generators using (targetTorus)
import DeloopS3.Bridge.CoverChains.Words as Words
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Cert.Check as Ch

abstract
  difference-scale : (a b t : ℤ)
    → a Z.· t Z.- b Z.· t ≡ (a Z.- b) Z.· t
  difference-scale a b t = cong (a Z.· t Z.+_) (Z.-DistL· b t)
    ∙ sym (Z.·DistL+ a (Z.- b) t)

  raw-scale : (c : ShortCase) (v : fst (Tori c)) (t : ℤ)
    (s : Sh c) (g : Generator)
    → fst (rawIncidence c) (λ b → v b Z.· t) (s , g)
      ≡ fst (rawIncidence c) v (s , g) Z.· t
  raw-scale c v t s ga = difference-scale
    (v (A , orbit c A s)) (v (C , orbit c C s)) t
  raw-scale c v t s gb = difference-scale
    (v (B , orbit c B s)) (v (C , orbit c C (nextSheet c s gb))) t

  Dhat-basis-scaled : (c : ShortCase) (b : Bdy c) (t : ℤ) (j : Petal c)
    → fst (Dhat c) (λ b′ → Words.basis c b b′ Z.· t) j
      ≡ Words.initialExponent c b j Z.· t
  Dhat-basis-scaled c b t j = raw-scale c (Words.basis c b) t
    (fst (nonTree c j)) (snd (nonTree c j))
    ∙ cong (Z._· t) (Words.Dhat-basis-initial-word c b j)

  -- Literal A/B/C word columns, retaining the generator names 1 and 2.
  base-word-column : (k : Kind) (t : ℤ)
    → (Words.wordExponent 1 (Ch.kindWord k) Z.· t ,
       Words.wordExponent 2 (Ch.kindWord k) Z.· t)
      ≡ fst Base.D (targetTorus k t)
  base-word-column A t = ΣPathP (Z.·IdL t , Z.·AnnihilL t)
  base-word-column B t = ΣPathP (Z.·AnnihilL t , Z.·IdL t)
  base-word-column C t = ΣPathP (Z.pos0+ (Z.- t) , Z.pos0+ (Z.- t))
