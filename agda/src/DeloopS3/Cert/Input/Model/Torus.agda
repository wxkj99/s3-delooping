{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Input.Model.Torus where

-- Torus maps into a groupoid; only the target supplies a higher filler.
-- Neither the source torus nor the Seifert pushout is truncated.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import DeloopS3.Move.CancelMinimal using (C; T²; 0C)
import DeloopS3.Cover.Orientation.CircleModel as Circle

module BasedTorus {X : Type₀} (gpd : isGroupoid X)
  (f g : T² → X) (p : f (0C , 0C) ≡ g (0C , 0C))
  (u-square : PathP (λ i → f (Circle.hC i , 0C) ≡ g (Circle.hC i , 0C)) p p)
  (t-square : PathP (λ i → f (0C , Circle.hC i) ≡ g (0C , Circle.hC i)) p p) where

  private
    on : (u t : S¹) → f (Circle.circleToC u , Circle.circleToC t)
      ≡ g (Circle.circleToC u , Circle.circleToC t)
    on base base = p
    on (loop i) base = u-square i
    on base (loop j) = t-square j
    on (loop i) (loop j) = isSet→SquareP
      (λ i j → gpd (f (Circle.hC i , Circle.hC j)) (g (Circle.hC i , Circle.hC j)))
      t-square t-square u-square u-square i j

  seam : (z : T²) → f z ≡ g z
  seam (u , t) = subst (λ z → f z ≡ g z)
    (λ i → Circle.circle-retraction u i , Circle.circle-retraction t i)
    (on (Circle.CToCircle u) (Circle.CToCircle t))

  abstract
    seam-base : seam (0C , 0C) ≡ p
    seam-base = substRefl {B = λ z → f z ≡ g z} p
