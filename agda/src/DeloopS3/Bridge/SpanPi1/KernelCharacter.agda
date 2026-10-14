{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.KernelCharacter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
import Cubical.HITs.PropositionalTruncation as PT
import DeloopS3.Bridge.OriginalSpan as OS
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)
open import DeloopS3.Bridge.SpanPi1.Coordinates
open import DeloopS3.Bridge.SpanPi1.CoverWitnesses using (subgroup-image-nonabelian; normal-core-lift)
open import DeloopS3.Bridge.SpanPi1.Character using
  (KleinCharacter; rotationCharacter; dihedral-character-rigid-merely)

abstract
  -- This is the algebraic implication, explicitly named as such. The
  -- unconditional source package is a separate geometric theorem.
  cover-kernel-character-from-source : (c : ShortCase)
    (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
    → PT.∥ KleinCharacter (K c) (qCoverπ c rp) ∥₁
    → (u : fst (K c))
    → fst (qCoverπ c rp) u
      ≡ fst (rotationCharacter c) (fst (subgroupπ c) u)
  cover-kernel-character-from-source c rp source =
    dihedral-character-rigid-merely c (K c) (qCoverπ c rp) (subgroupπ c)
      source (subgroup-image-nonabelian c)

  normal-core-in-kernel-from-source : (c : ShortCase)
    (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
    → PT.∥ KleinCharacter (K c) (qCoverπ c rp) ∥₁
    → Σ[ u ∈ fst (K c) ]
        (fst (projectionπ c) u ≡ w c) × (fst (qCoverπ c rp) u ≡ zero₂)
  normal-core-in-kernel-from-source c rp source =
    normal-core-lift c .fst , normal-core-lift c .snd .fst ,
    (cover-kernel-character-from-source c rp source (normal-core-lift c .fst)
      ∙ normal-core-lift c .snd .snd)

-- The geometric input is proved separately in SourceCharacter.agda.
-- Simple instantiates this module with that unconditional theorem; keeping
-- the algebra separate prevents unfolding the source equivalence here.
module FromSource
  (source-character : (c : ShortCase)
    (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
    → PT.∥ KleinCharacter (K c) (qCoverπ c rp) ∥₁) where

  abstract
    cover-kernel-character : (c : ShortCase)
      (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
      → (u : fst (K c))
      → fst (qCoverπ c rp) u
        ≡ fst (rotationCharacter c) (fst (subgroupπ c) u)
    cover-kernel-character c rp = cover-kernel-character-from-source c rp (source-character c rp)
