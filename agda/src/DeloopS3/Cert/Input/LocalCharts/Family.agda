{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Family where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM
import Cubical.HITs.S1 as S1
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimalCore using (ua-equiv-family)
import DeloopS3.Cover.CircleOrbit as CO
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Interpret.Realization as R

abstract
  degree-mul : (l : ℕ) (u : R.C) → CO.degree l u ≡ R.mulC (Z.pos l) u
  degree-mul l = EM.elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ n i j → emloop (Z.pos l Z.· n) i)

  degree-mul-base : (l : ℕ) → degree-mul l R.0C ≡ refl
  degree-mul-base l = refl


-- Circle induction, with the specified equivalence at zero retained.
module Comparison {X : Type₀} (α : CO.FinitePermutation X)
  (orbit : CO.CyclicOrbitData α) (F : R.C → Type₀)
  (e : X ≃ F R.0C)
  (square : (x : X) → subst F Circle.hC (equivFun e x)
    ≡ equivFun e (CO.FinitePermutation.permutation α .fst x)) where
  module M = CO.CircleConstruction α orbit
  module O = CO.CyclicOrbitData orbit

  private
    on : (z : S1.S¹) → M.circleFamily (Circle.circleToC z) .fst ≃ F (Circle.circleToC z)
    on S1.base = e
    on (S1.loop i) = ua-equiv-family
      (O.action .fst (CO.residue O.modulus-1 .fst (Z.pos 1)))
      (λ j → F (Circle.hC j)) e e
      (λ x → toPathP (square x ∙ cong (λ a → equivFun e (equivFun a x))
        (sym O.generator-action))) i

  comparison : (u : R.C) → M.circleFamily u .fst ≃ F u
  comparison u = subst (λ v → M.circleFamily v .fst ≃ F v)
    (Circle.circle-retraction u) (on (Circle.CToCircle u))

  abstract
    comparison-base : comparison R.0C ≡ e
    comparison-base = transportRefl e

  total : M.CircleCover ≃ Σ R.C F
  total = Σ-cong-equiv-snd comparison

  circles : (O.Rep × R.C) ≃ Σ R.C F
  circles = compEquiv (CO.MarkedCoverComparison.e (CO.circleOrbitCover α orbit)) total

  projection : (r : O.Rep) (u : R.C)
    → equivFun circles (r , u) .fst ≡ CO.degree (O.length r) u
  projection r u = refl

  abstract
    circles-base : (r : O.Rep)
      → equivFun circles (r , R.0C) ≡ (R.0C , equivFun e (O.repr r))
    circles-base r i = R.0C , equivFun (comparison-base i) (O.repr r)

  positive : O.Rep × R.C → Σ R.C F
  positive (r , u) = R.mulC (Z.pos (O.length r)) u ,
    subst F (degree-mul (O.length r) u) (equivFun circles (r , u) .snd)

  abstract
    positive-agrees : (z : O.Rep × R.C) → equivFun circles z ≡ positive z
    positive-agrees (r , u) i = degree-mul (O.length r) u i ,
      subst-filler F (degree-mul (O.length r) u) (equivFun circles (r , u) .snd) i

    positive-isEquiv : isEquiv positive
    positive-isEquiv = subst isEquiv (funExt positive-agrees) (circles .snd)

    positive-base-fibre : (r : O.Rep)
      → positive (r , R.0C) .snd ≡ equivFun e (O.repr r)
    positive-base-fibre r =
      cong (λ p → subst F p (equivFun circles (r , R.0C) .snd)) (degree-mul-base (O.length r))
      ∙ transportRefl (equivFun circles (r , R.0C) .snd)
      ∙ cong (λ d → equivFun d (O.repr r)) comparison-base

    positive-base : (r : O.Rep)
      → positive (r , R.0C) ≡ (R.0C , equivFun e (O.repr r))
    positive-base r i = R.0C , positive-base-fibre r i

  positiveCircles : (O.Rep × R.C) ≃ Σ R.C F
  positiveCircles = positive , positive-isEquiv

abstract
  circle-connected : (u : R.C) → PT.∥ R.0C ≡ u ∥₁
  circle-connected u = PT.map (λ p → cong Circle.circleToC p ∙ Circle.circle-retraction u)
    (S1.isConnectedS¹ (Circle.CToCircle u))

  torus-connected : (z : R.T²) → PT.∥ (R.0C , R.0C) ≡ z ∥₁
  torus-connected (u , t) = PT.rec2 PT.squash₁
    (λ p q → PT.∣ (λ i → p i , q i) ∣₁) (circle-connected u) (circle-connected t)
