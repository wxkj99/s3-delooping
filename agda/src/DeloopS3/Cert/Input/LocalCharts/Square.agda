{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Square where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
import Cubical.Data.Nat as N
import Cubical.Data.Int as Z
open import Cubical.HITs.Pushout.Base using (inr; push)
open import DeloopS3.Cover.Cosets using (CosetFamily)
open import DeloopS3.Cert.Input.Model
open import DeloopS3.Cert.Input.Orbits using (short-orbit-modulus; orbit-factor)
open import DeloopS3.Cert.Input.LocalCharts.Actual
open import DeloopS3.Cert.Input.LocalCharts.Index
open import DeloopS3.Cert.Input.LocalCharts.Charts
open import DeloopS3.Cert.Input.LocalCharts.Lift
open import DeloopS3.Cert.Input.LocalCharts.Family using (torus-connected)
open import DeloopS3.Cert.Input.LocalCharts.Row using (module Row)
import DeloopS3.Cover.CircleOrbit as CO
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R

componentCore : (c : ShortCase) (k : Ch.Kind) → Bd c k × R.C → R.Span.R (FlatSpan c)
componentCore c k z = (k , core-positive c k z .fst) , core-positive c k z .snd

componentOverlap : (c : ShortCase) (k : Ch.Kind) → Bd c k × R.T² → R.Span.O (FlatSpan c)
componentOverlap c k (b , u , t) = (k , boundary-positive c k (b , u) .fst , t) ,
  boundary-positive c k (b , u) .snd

abstract
  local-factor : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → localOrder c k ≡ suc (ellPred c k b) N.· suc (orderPred c k b)
  local-factor c k b = sym (short-orbit-modulus c k) ∙ orbit-factor c k b

  -- This is transport along THE push of BaseSpan, not an identity seam
  -- substituted by hand. Its equality at zero uses classifier-seam-base.
  flat-seam-base : (c : ShortCase) (k : Ch.Kind)
    (q : BoundaryFamily c k R.0C)
    → subst (Q c) (push (k , R.0C , R.0C)) q ≡ q
  flat-seam-base c k q = cong
    (λ p → subst (λ v → CosetFamily (j c) v .fst) p q)
    (classifier-seam-base c k) ∙ transportRefl q

module LiftedRow (c : ShortCase) (k : Ch.Kind) (b : Bd c k) where
  module Base = Row (localWeight c k) (suc (ellPred c k b))
    (suc (orderPred c k b)) (localOrder c k) (local-factor c k b)

  f g : R.T² → R.Span.R (FlatSpan c)
  f z = componentCore c k (b , row (localWeight c k) (suc (orderPred c k b)) z)
  g z = R.Span.right (FlatSpan c) (componentOverlap c k (b , z))

  h : (z : R.T²) → fst (f z) ≡ fst (g z)
  h z i = k , Base.homotopy z i

  abstract
    base-fibre : f (R.0C , R.0C) .snd ≡ g (R.0C , R.0C) .snd
    base-fibre = core-fibre-base c k b ∙ sym
      (flat-seam-base c k (boundary-positive c k (b , R.0C) .snd)
       ∙ boundary-fibre-base c k b)

  based : f (R.0C , R.0C) ≡ g (R.0C , R.0C)
  based i = (k , R.0C) , base-fibre i

  abstract
    based-over : cong fst based ≡ h (R.0C , R.0C)
    based-over = sym (cong (λ p i → k , p i) Base.homotopy-base)

    lifted : Σ[ H ∈ ((z : R.T²) → f z ≡ g z) ]
      ((z : R.T²) → cong fst (H z) ≡ h z)
    lifted = based-lift-unique {B = Ch.Kind × R.C} {X = R.T²}
      (λ y → Q c (inr y))
      (λ y → CosetFamily (j c) (ρ-M c (inr y)) .snd)
      (R.0C , R.0C) torus-connected f g h based based-over

  square : (z : R.T²) → f z ≡ g z
  square = lifted .fst

  square-over : (z : R.T²) → cong fst (square z) ≡ h z
  square-over = lifted .snd

  abstract
    -- Faithfulness is used only AFTER constructing the homotopy from
    -- its based lift. It verifies that the chosen based path is retained.
    square-base : square (R.0C , R.0C) ≡ based
    square-base = CO.cover-path-ext
      (λ y → CosetFamily (j c) (ρ-M c (inr y)))
      (square (R.0C , R.0C)) based
      (square-over (R.0C , R.0C) ∙ sym based-over)

abstract
  coreChart-value : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
    → equivFun (coreChart c) (b , u)
      ≡ componentCore c (kindAt c b) (localAt c b , u)
  coreChart-value c b u = refl


  overlapChart-value : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u t : R.C)
    → equivFun (overlapChart c) (b , u , t)
      ≡ componentOverlap c (kindAt c b) (localAt c b , u , t)
  overlapChart-value c b u t = refl

  face-row : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u t : R.C)
    → R.mulC (R.int (Ch.faceWeight (R.faceAt (S₀ c) b))) u R.+C
        R.mulC (Z.pos (Ch.faceOrder (R.faceAt (S₀ c) b))) t
      ≡ row (localWeight c (kindAt c b)) (suc (orderPred c (kindAt c b) (localAt c b))) (u , t)
  face-row c b u t i = R.mulC (weight-index (face-data c b) i) u R.+C
    R.mulC (Z.pos (order-index (face-data c b) i)) t

  rightSquare : (c : ShortCase) (z : R.O (S₀ c))
    → equivFun (coreChart c) (R.right (S₀ c) z)
      ≡ R.Span.right (FlatSpan c) (equivFun (overlapChart c) z)
  rightSquare c (b , u , t) =
    cong (λ v → equivFun (coreChart c) (b , v)) (face-row c b u t)
    ∙ LiftedRow.square c (kindAt c b) (localAt c b) (u , t)
