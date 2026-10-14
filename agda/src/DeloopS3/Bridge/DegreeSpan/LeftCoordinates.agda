{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCoordinates where

-- Actual left coordinates and matrix squares, assembled from separate modules.
open import DeloopS3.Bridge.DegreeSpan.LeftCoordinateSource public
  using (eLs ; source-left ; source-component-H₂ ; source-left-on-component)
open import DeloopS3.Bridge.DegreeSpan.LeftCoordinateTarget public
  using (eLt ; target-left ; target-component-H₂)
