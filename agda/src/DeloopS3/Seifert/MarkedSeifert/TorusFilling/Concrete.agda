{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Torus filling from the constructed Seifert pushout and boundary words,
-- parametrized by a marked W ≃ RelJR comparison. WRelJR supplies that
-- comparison; TorusFilling reexports the instance without an import cycle.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.Concrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
import DeloopS3.Seifert.MarkedSeifert.WEquiv as Checked
import DeloopS3.Seifert.MarkedSeifert.WInterface as W
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.HITEquiv
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops using (based-sym)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third

module CheckedFromNielsen
  (HYPOTHESIS : W.W ≃ W.RelJR)
  (baseComparison : HYPOTHESIS .fst Checked.w₀ ≡ W.vertex)
  (xComparison : based baseComparison (cong (HYPOTHESIS .fst) Checked.xW) ≡ W.j)
  (yComparison : based baseComparison (cong (HYPOTHESIS .fst) Checked.yW) ≡ W.j ∙ sym W.r)
  where

  private
    E : W.W → W.RelJR
    E = HYPOTHESIS .fst

  abstract
    third-meridian : based baseComparison (cong (E ∘ Checked.bW) uT)
      ≡ sym (W.j ∙ (W.j ∙ sym W.r))
    third-meridian = cong (based baseComparison ∘ cong E) Checked.boundary-meridian
      ∙ cong (based baseComparison ∘ sym) (cong-∙ E Checked.xW Checked.yW)
      ∙ based-sym baseComparison (cong E Checked.xW ∙ cong E Checked.yW)
      ∙ cong sym (based-comp baseComparison (cong E Checked.xW) (cong E Checked.yW)
          ∙ cong₂ _∙_ xComparison yComparison)

    third-fibre : based baseComparison (cong (E ∘ Checked.bW) vT) ≡ W.j ∙ W.j
    third-fibre = cong (based baseComparison ∘ cong E) Checked.boundary-fibre-x
      ∙ cong (based baseComparison) (cong-∙ E Checked.xW Checked.xW)
      ∙ based-comp baseComparison (cong E Checked.xW) (cong E Checked.xW)
      ∙ cong₂ _∙_ xComparison xComparison

  markedW : W.WComparison Checked.M22e
  markedW .W.WComparison.bW = Checked.bW
  markedW .W.WComparison.W≃RelJR = HYPOTHESIS
  markedW .W.WComparison.thirdStaged = Checked.thirdStaged
  markedW .W.WComparison.boundary-base = baseComparison
  markedW .W.WComparison.boundary-u = third-meridian
  markedW .W.WComparison.boundary-v = third-fibre

  open FromW Checked.M22e markedW public

  abstract
    -- Based forms of W≃Kinv-x and W≃Kinv-y, with the
    -- actual xW,yW and their retained connecting-edge conjugation.
    W≃Kinv-x : based pK (cong WtoKinv Checked.xW) ≡ j
    W≃Kinv-x = sym (cong-based relToKinv baseComparison (cong E Checked.xW))
      ∙ cong (cong relToKinv) xComparison

    W≃Kinv-y : based pK (cong WtoKinv Checked.yW) ≡ j ∙ sym r
    W≃Kinv-y = sym (cong-based relToKinv baseComparison (cong E Checked.yW))
      ∙ cong (cong relToKinv) yComparison ∙ cong-∙ relToKinv W.j (sym W.r)
