{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter.Cap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; T²)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus using (Kinv)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap using (λ₂)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill)
open import DeloopS3.Seifert.TwistedBundle.Base using (A; Ksign; λA)
import DeloopS3.Seifert.MarkedSeifert.Final as Final
open import DeloopS3.Seifert.MarkedSeifert.DescentChart.Finish using (descentChart)
import DeloopS3.Seifert.TwistedBundle.Flattening as Flat
import DeloopS3.Seifert.TwistedBundle.SmallChart as Small
import DeloopS3.Seifert.TwistedBundle.Coherent as Coherent
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)

-- The geometric equivalence here need not compute any loop of Done.
-- We only retain its right vertex, which is visibly a cap fibre.
module Geometry (e : ℤ) where
  module F = Flat.Total e
  module S = Small.Filling e

  abstract
    fill-small : Fill e ≃ Final.SmallSpan.SmallFill e
    fill-small = pushoutEquiv λ₂ (row e (pos 1)) λA S.rowShift
      Final.torusCoverEquiv (Final.DescentChart.total descentChart) (idEquiv C)
      (Final.DescentChart.boundary descentChart
        ∙ cong (λA ∘_) (sym Final.torusCoverEquiv-map))
      (Final.sign-row e ∙ cong (S.rowShift ∘_) (sym Final.torusCoverEquiv-map))

    fill-small-core : (t : C) → fst fill-small (inr t) ≡ inr t
    fill-small-core t = refl

    coherent-small : F.Filling ≃ Final.SmallSpan.SmallFill e
    coherent-small = pushoutEquiv F.left F.right λA S.rowShift
      S.overlapTotal S.leftTotal S.rightTotal
      (Final.SmallSpan.left-square e) (Final.SmallSpan.right-square e)

    coherent-small-core : (t : C)
      → invEq coherent-small (inr t) ≡ inr (invEq S.rightTotal t)
    coherent-small-core t = refl

    coherent-core-null : (z : F.R)
      → Bundle.pₑ e (fst F.fillToTotal (inr z)) ≡ inr tt
    coherent-core-null (T , y , t) = F.fillToTotal-over (inr (T , y , t))
      ∙ Coherent.quotient-agrees (T , inr y)

  abstract
    equivalence : Fill e ≃ Bundle.Mₑ e
    equivalence = compEquiv fill-small (compEquiv (invEquiv coherent-small) F.fillToTotal)

    projection : Fill e → RP²
    projection = Bundle.pₑ e ∘ fst equivalence

    projection-map : projection ≡ Bundle.pₑ e ∘ fst equivalence
    projection-map = refl

    core-null : (t : C) → projection (inr t) ≡ inr tt
    core-null t = cong (Bundle.pₑ e ∘ fst F.fillToTotal ∘ invEq coherent-small)
      (fill-small-core t)
      ∙ cong (Bundle.pₑ e ∘ fst F.fillToTotal) (coherent-small-core t)
      ∙ coherent-core-null (invEq S.rightTotal t)
