{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.SpanProjection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
import DeloopS3.Cert.Interpret.Realization as R

-- Prove constructor coherence before instantiating the finite charts.
-- In particular no conversion step here unfolds their semantic fibres.
module Prescribed {D E : R.Span ℓ-zero ℓ-zero ℓ-zero}
  (e : R.SpanEquiv D E) {M : Type₀} (π : R.Total E → M) where
  open R.SpanEquiv e
  module Span = R.SpanMap e

  seam : (z : R.Span.O D)
    → Path (R.Total E)
        (inl (equivFun leftVertex (R.Span.left D z)))
        (inr (equivFun rightVertex (R.Span.right D z)))
  seam z = cong inl (leftSquare z)
    ∙∙ push (equivFun overlapEquiv z)
    ∙∙ sym (cong inr (rightSquare z))

  projection : R.Total D → M
  projection (inl x) = π (inl (equivFun leftVertex x))
  projection (inr y) = π (inr (equivFun rightVertex y))
  projection (push z i) = π (seam z i)

  abstract
    projection-agrees : (x : R.Total D)
      → projection x ≡ π (equivFun Span.spanEquiv x)
    projection-agrees (inl x) = sym (cong π (Span.spanEquiv-inl x))
    projection-agrees (inr y) = sym (cong π (Span.spanEquiv-inr y))
    projection-agrees (push z i) j = π (Span.spanEquiv-push z (~ j) i)

    projection-push : (z : R.Span.O D)
      → cong projection (push z)
        ≡ (cong π (cong inl (leftSquare z))
           ∙∙ cong π (push (equivFun overlapEquiv z))
           ∙∙ sym (cong π (cong inr (rightSquare z))))
    projection-push z = cong-∙∙ π (cong inl (leftSquare z))
      (push (equivFun overlapEquiv z)) (sym (cong inr (rightSquare z)))
