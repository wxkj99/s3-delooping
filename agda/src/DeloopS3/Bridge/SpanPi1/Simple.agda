{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.Simple where

open import DeloopS3.Bridge.SpanPi1.Seam public
open import DeloopS3.Bridge.SpanPi1.Coordinates public
open import DeloopS3.Bridge.SpanPi1.CoverWitnesses public
open import DeloopS3.Bridge.SpanPi1.KernelCharacter public
open import DeloopS3.Bridge.SpanPi1.SourceInclusion public
open import DeloopS3.Bridge.SpanPi1.RP2Pi1 public using (RP²-π₁)
open import DeloopS3.Bridge.SpanPi1.SourceCharacter public using (source-character)

module SourceRigidity = FromSource source-character
open SourceRigidity public using (cover-kernel-character)
