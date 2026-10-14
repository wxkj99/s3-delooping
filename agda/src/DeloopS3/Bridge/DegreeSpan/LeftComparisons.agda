{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftComparisons where

-- This direct record construction checks all actual CW endpoints and all
-- coordinate choices against the final consumer; no transport is implicit.
open import DeloopS3.Cert.Input.Model using (ShortCase)
open import DeloopS3.Bridge.DegreeSpan.CoverDegreeFromH2 using (CoverH2Comparisons)
import DeloopS3.Bridge.DegreeSpan.OverlapCoordinates as Overlap
import DeloopS3.Bridge.DegreeSpan.LeftCoordinates as Left

comparisons : (c : ShortCase) → CoverH2Comparisons c
CoverH2Comparisons.eOs (comparisons c) = Overlap.coordCover c
CoverH2Comparisons.eOt (comparisons c) = Overlap.coordBase c
CoverH2Comparisons.eLs (comparisons c) = Left.eLs c
CoverH2Comparisons.eLt (comparisons c) = Left.eLt c
CoverH2Comparisons.source-left (comparisons c) = Left.source-left c
CoverH2Comparisons.target-left (comparisons c) = Left.target-left c
CoverH2Comparisons.overlap-cover (comparisons c) = Overlap.overlap₂ c
