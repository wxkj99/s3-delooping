{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Row where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as N
import Cubical.Data.Int as Z
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (cong₂+₁)
open import DeloopS3.Cert.Input.Model using (row; row-u-loop; row-t-loop)
open import DeloopS3.Cert.Input.Model.Torus using (module BasedTorus)
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Interpret.Realization as R

-- The small row retains s, not l*s. Both circle coordinates are positive.
module Row (s : Z.ℤ) (l d n : ℕ) (factor : n ≡ l N.· d) where
  f g : R.T² → R.C
  f (u , t) = R.mulC (Z.pos l) (row s d (u , t))
  g (u , t) = row s n (R.mulC (Z.pos l) u , t)

  abstract
    f-u : cong (λ u → f (u , R.0C)) Circle.hC ≡ emloop (Z.pos l Z.· s)
    f-u = cong (cong (R.mulC (Z.pos l))) (row-u-loop s d)

    g-u : cong (λ u → g (u , R.0C)) Circle.hC ≡ emloop (s Z.· Z.pos l)
    g-u = cong₂+₁ {G = ℤAbGroup} (emloop (s Z.· (Z.pos l Z.· Z.pos 1))) refl
      ∙ sym (rUnit (emloop (s Z.· (Z.pos l Z.· Z.pos 1))))
      ∙ cong (λ z → emloop (s Z.· z)) (Z.·IdR (Z.pos l))

    f-t : cong (λ t → f (R.0C , t)) Circle.hC ≡ emloop (Z.pos n)
    f-t = cong (cong (R.mulC (Z.pos l))) (row-t-loop s d)
      ∙ cong emloop (sym (Z.pos·pos l d) ∙ cong Z.pos (sym factor))

    g-t : cong (λ t → g (R.0C , t)) Circle.hC ≡ emloop (Z.pos n)
    g-t = row-t-loop s n

    u-square : cong (λ u → f (u , R.0C)) Circle.hC ≡ cong (λ u → g (u , R.0C)) Circle.hC
    u-square = f-u ∙ cong emloop (Z.·Comm (Z.pos l) s) ∙ sym g-u

    t-square : cong (λ t → f (R.0C , t)) Circle.hC ≡ cong (λ t → g (R.0C , t)) Circle.hC
    t-square = f-t ∙ sym g-t

  module T = BasedTorus emsquash f g refl
    (λ i j → u-square j i) (λ i j → t-square j i)

  homotopy : (z : R.T²) → f z ≡ g z
  homotopy = T.seam

  abstract
    homotopy-base : homotopy (R.0C , R.0C) ≡ refl
    homotopy-base = T.seam-base
