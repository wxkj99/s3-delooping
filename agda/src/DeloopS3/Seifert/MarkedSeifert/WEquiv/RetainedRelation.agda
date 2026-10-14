{-# OPTIONS --safe --cubical #-}

-- Retain the W relation at BOTH R1 cancellations.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.RetainedRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelLoopCell
open import DeloopS3.Move.CancelGeneral using (module General; module ReplaceLeft)
open import DeloopS3.Move.CancelMinimal using (T²; C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Nielsen

wordXY : qxy ≡ qxy
wordXY = (xLoop ∙ xLoop) ∙ sym (yLoop ∙ yLoop)
wordJR : qjr ≡ qjr
wordJR = (jLoop ∙ jLoop) ∙ sym ((jLoop ∙ sym rLoop) ∙ (jLoop ∙ sym rLoop))

FilledXY FilledJR : Type₀
FilledXY = CofibLoop qxy wordXY
FilledJR = CofibLoop qjr wordJR

private
  collapse : S¹ → Unit
  collapse _ = tt
  retainedA : S¹ → A
  retainedA = incQ ∘ circleMap wordXY
  retainedB : S¹ → B
  retainedB = permute ∘ retainedA

-- These are the General.cancel-all constructions, including
-- their H-on-Q/cell cubes and their exact corrected surviving seams.
module FirstKept = General Gxy qxy yLoop (sym xLoop) plus retainedA collapse
module SecondKept = General Gjr qjr refl (rLoop ∙ sym jLoop) plus retainedB collapse

private
  commonTriangle : (z : S¹ ⊎ S¹)
    → regroup .fst (FirstKept.T.all-left z) ≡ SecondKept.T.all-left z
  commonTriangle (left z) = relator-change z
  commonTriangle (right z) = funExt⁻ regroup-map (retainedA z)

  mappedWord : cong forward wordXY ≡ wordJR
  mappedWord = cong-∙ forward (xLoop ∙ xLoop) (sym (yLoop ∙ yLoop))
    ∙ cong₂ _∙_ (cong-∙ forward xLoop xLoop)
      (cong sym (cong-∙ forward yLoop yLoop))

  mappedCircle : (z : S¹) → forward (circleMap wordXY z) ≡ circleMap wordJR z
  mappedCircle base = refl
  mappedCircle (loop i) k = mappedWord k i

  retract-graph : (z : Gxy)
    → Second.retractMap (inl (permute (incQ z))) ≡ forward z
  retract-graph (incQ s) = refl
  retract-graph (x i) = refl

  secondTriangle : (z : S¹) → SecondKept.u′ z ≡ circleMap wordJR z
  secondTriangle z = funExt⁻ Second.canonical-agrees (inl (retainedB z))
    ∙ retract-graph (circleMap wordXY z) ∙ mappedCircle z

abstract
  commonFilledN : FirstKept.Oall ≃ SecondKept.Oall
  commonFilledN = pushoutEquiv FirstKept.T.all-left FirstKept.T.all-right
    SecondKept.T.all-left SecondKept.T.all-right
    (idEquiv (S¹ ⊎ S¹)) regroup (idEquiv (Unit ⊎ Unit))
    (funExt commonTriangle) (funExt λ { (left z) → refl ; (right z) → refl })

  firstStandard : FirstKept.O′ ≃ FilledXY
  firstStandard = pushoutEquiv FirstKept.u′ collapse (circleMap wordXY) collapse
    (idEquiv S¹) (idEquiv Gxy) (idEquiv Unit)
    (λ i z → First.P.rj i (circleMap wordXY z)) refl

  secondStandard : SecondKept.O′ ≃ FilledJR
  secondStandard = pushoutEquiv SecondKept.u′ collapse (circleMap wordJR) collapse
    (idEquiv S¹) (idEquiv Gjr) (idEquiv Unit) (funExt secondTriangle) refl

  filledNielsen : FilledXY ≃ FilledJR
  filledNielsen = compEquiv (invEquiv firstStandard)
    (compEquiv FirstKept.cancel-all (compEquiv commonFilledN
      (compEquiv (invEquiv SecondKept.cancel-all) secondStandard)))

-- In particular a WHOLE torus may be carried across the filled
-- equivalence. No factorization through either free graph is requested.
module CarryTorus (boundary : T² → FilledXY) (filling : T² → C) where
  boundaryJR : T² → FilledJR
  boundaryJR = filledNielsen .fst ∘ boundary
  abstract
    carryTorus : Pushout boundary filling ≃ Pushout boundaryJR filling
    carryTorus = pushoutEquiv boundary filling boundaryJR filling
      (idEquiv T²) filledNielsen (idEquiv C) refl refl

  -- Formula (1.1), in the backward direction, with its actual homotopy.
  module Back = ReplaceLeft filledNielsen (invEq filledNielsen)
    (secEq filledNielsen) boundaryJR filling
  corrected-seam : (t : T²)
    → Back.F (inl (invEq filledNielsen (boundaryJR t))) ≡ Back.F (inr (filling t))
  corrected-seam t = cong Back.F (push t)

  private
    targetLeft : FilledJR → Back.Ostage
    targetLeft = inl

  corrected-seam-formula : (t : T²)
    → corrected-seam t ≡
      cong targetLeft (secEq filledNielsen (boundaryJR t)) ∙ push t
  corrected-seam-formula t = refl
