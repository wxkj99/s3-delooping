{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Left where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import DeloopS3.Cert.Input.Model using (ShortCase; S₀; gs; FlatSpan; bdAllAt)
open import DeloopS3.Cert.Input.Graph.Maps using (expand)
open import DeloopS3.Cert.Input.Graph.Chart using (graph-chart)
open import DeloopS3.Cert.Input.Graph.Total
open import DeloopS3.Cert.Input.Initial.Actual using (overlapGraph)
open import DeloopS3.Cert.Input.Initial.Marked using (marked-boundary)
open import DeloopS3.Cert.Input.Initial.Faces
import DeloopS3.Cert.Input.LocalCharts.Charts as Local
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch

-- Literal reassociation into the left dependent sum of FlatSpan.
leftRearrange : (c : ShortCase) → GraphTotal c × R.C → R.Span.L (FlatSpan c)
leftRearrange c ((x , q) , t) = (x , t) , q

leftRearrangeEquiv : (c : ShortCase) → (GraphTotal c × R.C) ≃ R.Span.L (FlatSpan c)
leftRearrangeEquiv c = isoToEquiv (iso (leftRearrange c)
  (λ { ((x , t) , q) → (x , q) , t }) (λ _ → refl) (λ _ → refl))

leftChart : (c : ShortCase) → R.L (S₀ c) ≃ R.Span.L (FlatSpan c)
leftChart c = compEquiv
  (≃-× (compEquiv (graph-chart c) (liftToTotal c , liftToTotal-isEquiv c)) (idEquiv R.C))
  (leftRearrangeEquiv c)

abstract
  leftChart-value : (c : ShortCase) (x : R.Rose (gs c)) (t : R.C)
    → equivFun (leftChart c) (x , t) ≡ leftRearrange c (liftToTotal c (expand c x) , t)
  leftChart-value c x t = refl

  overlap-left-value : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u t : R.C)
    → R.Span.left (FlatSpan c) (equivFun (Local.overlapChart c) (b , u , t))
      ≡ leftRearrange c (overlapGraph c b u , t)
  overlap-left-value c b u t = refl

  leftSquare : (c : ShortCase) (z : R.O (S₀ c))
    → equivFun (leftChart c) (R.left (S₀ c) z)
      ≡ R.Span.left (FlatSpan c) (equivFun (Local.overlapChart c) z)
  leftSquare c (b , u , t) =
    cong (equivFun (leftChart c))
      (λ i → R.wordCircle (gs c) (initial-word c b i) u , initial-fibre c b u t i)
    ∙ leftChart-value c (R.wordCircle (gs c) (Ch.boundaryWord (bdAllAt c b)) u) t
    ∙ cong (λ q → leftRearrange c (q , t)) (marked-boundary c b u)
    ∙ sym (overlap-left-value c b u t)
