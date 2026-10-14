{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.FiniteDim where

-- Finite-dimensional CW bounds and homology vanishing above the bound.
-- Finite≤ d uses finCWskel at stage suc d: stage 1 is the 0-skeleton.
open import DeloopS3.Bridge.Recognition.Notation public using
  (CW₀ ; Finite≤ ; Hzero ; Hiso ; finite≤→isCW ; finite≤→isFinCW)

-- Dimension extracts the sharp bound from CWPushout.pushoutSkel via
-- stabilization of pushoutA, after strictification and cellular
-- approximation.  The cofibre case uses the 0-dimensional Unit witness.
open import DeloopS3.Bridge.Recognition.Dimension public using
  (pushout-finite≤ ; cofib-finite≤ ; sphere-finite≤ ; unit-finite≤)

-- Replace a stabilizing skeleton by its finite subcomplex; its cellular
-- chains vanish above the bound.  The existing homology functor and
-- propositionality of isCW identify the result with the supplied CW₀.
open import DeloopS3.Bridge.Recognition.HomologyDimension public using
  (finite≤-homology-above)

-- These are Local.EI's actual HIT cofibres, not new presentations.
open import DeloopS3.Local.EI public using (BottomMoore ; Moore)

-- BottomMoore has dimension at most 3, and Moore m 2 at most 4.
-- Their CW witnesses retain the actual HITs as definitional endpoints.
open import DeloopS3.Bridge.Recognition.Models public using
  (bottom-finite≤ ; moore3-finite≤ ; bottomCW ; moore3CW)
