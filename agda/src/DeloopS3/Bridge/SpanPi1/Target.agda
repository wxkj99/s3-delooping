{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.Target where

open import DeloopS3.Bridge.SpanPi1.TargetLoops public
open import DeloopS3.Bridge.SpanPi1.TargetRelations public
open import DeloopS3.Bridge.SpanPi1.TargetVertexGeneration public
open import DeloopS3.Bridge.SpanPi1.TargetGeneration public
open import DeloopS3.Bridge.SpanPi1.TargetNormal public

open import DeloopS3.Bridge.SpanPi1.TargetAssembly public

open import DeloopS3.Bridge.SpanPi1.TargetLiteral public

open import DeloopS3.Bridge.SpanPi1.TargetUniversal public

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (fst)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.SpanPi1.Simple as Simple
open import DeloopS3.Bridge.SpanPi1.Character using (rotationCharacter)

-- The wrapper combines the core lift and seam comparison with the
-- source-character theorem.
module FromCharacter
  (cover-kernel-character : (c : ShortCase)
    (rp : GroupEquiv (Simple.Π OS.R (Simple.qCover c (Simple.a₀ c))) Simple.C₂)
    → (u : fst (Simple.K c)) → fst (Simple.qCoverπ c rp) u
      ≡ fst (rotationCharacter c) (fst (Simple.subgroupπ c) u)) where
  private
    module Conclusion = Assembly Simple.normal-core-lift
      cover-kernel-character Simple.pushout-kills-kernel
  open Conclusion public using (X-simple)

-- Simple connectedness with no source-character or fibre-marking parameter.
import DeloopS3.Bridge.SpanPi1.SourceCharacter as Source
private
  module SourceRigidity = Simple.FromSource Source.source-character
open FromCharacter SourceRigidity.cover-kernel-character public using (X-simple)
