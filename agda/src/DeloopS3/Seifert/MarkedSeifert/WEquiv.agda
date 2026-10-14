{-# OPTIONS --safe --cubical #-}

-- The Seifert pushout, its first two fillings and retained torus boundary,
-- with untruncated mapping data and Nielsen changes of coordinates.
-- WRelJR constructs the marked W ≃ RelJR comparison from these interfaces.
module DeloopS3.Seifert.MarkedSeifert.WEquiv where

open import DeloopS3.Seifert.MarkedSeifert.WEquiv.FirstTwo public
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Boundary public
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge public
  using (WHit; circleModel; LoopSquare; squareAtRefl; equalityToRelator;
         module Mapping; transportBasedLoop)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Nielsen public
  using (Gxy; Gjr; qxy; qjr; xLoop; yLoop; jLoop; rLoop;
         nielsen; nielsen-map; forward; backward; forward-x; forward-y;
         backward-j; backward-r; inverse-formula)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.RetainedRelation public
  using (FilledXY; FilledJR; filledNielsen; module FirstKept;
         module SecondKept; module CarryTorus)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.NielsenMapping public
  using (module MappingJR)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Presentation
