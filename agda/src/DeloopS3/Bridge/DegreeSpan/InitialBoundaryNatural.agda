{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.InitialBoundaryNatural where

-- Naturality for the ACTUAL initial covering projection. The two LESs and
-- their equation are chosen jointly, and remain under PT throughout.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using (isCW)
open import Cubical.CW.Strictification using (strictCWskel)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; H̃ᶜʷ→ ; finite≤→isCW)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (GeometricPushoutLES ; SpanSequenceData)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Input.Initial.Endpoint as Init
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
import DeloopS3.Bridge.DegreeSpan.BoundaryDescent as Descent
import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Geometry as Geometry

-- Explicit witnesses on the original totals, not replacement pushouts or
-- skeletal realizations. Their only input is the Pieces finiteness.
source-isCW : (c : ShortCase) → isCW (R.T (Input.S₀ c))
source-isCW c = finite≤→isCW (Pieces.initial-finite c)

target-isCW : (c : ShortCase) → isCW (Input.M_G c)
target-isCW c = finite≤→isCW (Pieces.base-finite c)

source-CW target-CW : ShortCase → CW₀
source-CW c = R.T (Input.S₀ c) , source-isCW c
target-CW c = Input.M_G c , target-isCW c

-- The public target spells out both LES endpoints and both induced maps.
InitialBoundaryNatural : ShortCase → Type₁
InitialBoundaryNatural c =
  Σ[ sourceLES ∈ GeometricPushoutLES
    (Pieces.O₀CW c) (Pieces.L₀CW c) (Pieces.R₀CW c)
    (R.left (Input.S₀ c)) (R.right (Input.S₀ c)) (source-CW c) ]
  Σ[ targetLES ∈ GeometricPushoutLES
    (Pieces.OᵦCW c) (Pieces.LᵦCW c) (Pieces.RᵦCW c)
    (R.Span.left (Input.BaseSpan c)) (R.Span.right (Input.BaseSpan c)) (target-CW c) ]
    compGroupHom
      (H̃ᶜʷ→ {C = source-CW c} {D = target-CW c} 3 (Init.initialProjection c))
      (SpanSequenceData.boundary (snd targetLES) 2)
    ≡ compGroupHom
      (SpanSequenceData.boundary (snd sourceLES) 2)
      (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c))

private
  module Presentations (c : ShortCase) where
    module S = Pieces.FiniteCWSpan (Pieces.initial-pieces c)
    module T = Pieces.FiniteCWSpan (Pieces.base-pieces c)
    module F = Descent.Finite 3 3
      S.overlap-finite-model (fst S.left-model) (fst S.right-model)
      T.overlap-finite-model (fst T.left-model) (fst T.right-model)

    abstract
      -- Universal quantification is transported before the original map
      -- is supplied; there is no assumption about an unrelated comparison.
      all-maps : Descent.AllLegs
        (Pieces.O₀CW c) (Pieces.L₀CW c) (Pieces.R₀CW c)
        (Pieces.OᵦCW c) (Pieces.LᵦCW c) (Pieces.RᵦCW c)
      all-maps = Descent.descend-presentations
        (Pieces.O₀CW c) (Pieces.L₀CW c) (Pieces.R₀CW c)
        (Pieces.OᵦCW c) (Pieces.LᵦCW c) (Pieces.RᵦCW c)
        (strictCWskel (fst S.overlap-model))
        (strictCWskel (fst S.left-model))
        (strictCWskel (fst S.right-model))
        (strictCWskel (fst T.overlap-model))
        (strictCWskel (fst T.left-model))
        (strictCWskel (fst T.right-model))
        (compEquiv (snd S.overlap-model)
          (Geometry.strict-realisation-equiv (fst S.overlap-model)))
        (compEquiv (snd S.left-model)
          (Geometry.strict-realisation-equiv (fst S.left-model)))
        (compEquiv (snd S.right-model)
          (Geometry.strict-realisation-equiv (fst S.right-model)))
        (compEquiv (snd T.overlap-model)
          (Geometry.strict-realisation-equiv (fst T.overlap-model)))
        (compEquiv (snd T.left-model)
          (Geometry.strict-realisation-equiv (fst T.left-model)))
        (compEquiv (snd T.right-model)
          (Geometry.strict-realisation-equiv (fst T.right-model)))
        F.all-legs

abstract
  initial-boundary-natural : (c : ShortCase) → PT.∥ InitialBoundaryNatural c ∥₁
  initial-boundary-natural c = PT.map
    (λ (sourceLES , targetLES , natural) → sourceLES , targetLES ,
      (cong (λ p → compGroupHom
        (H̃ᶜʷ→ {C = source-CW c} {D = target-CW c} 3 p)
        (SpanSequenceData.boundary (snd targetLES) 2))
        (sym (Map.initial-total-agrees c)) ∙ natural))
    (Presentations.all-maps c
      (R.left (Input.S₀ c)) (R.right (Input.S₀ c))
      (R.Span.left (Input.BaseSpan c)) (R.Span.right (Input.BaseSpan c))
      (Map.initial-span-map c) (source-isCW c) (target-isCW c))
