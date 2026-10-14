{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Full torus maps, including their squares.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square; Square→compPath)
open import Cubical.Data.Sigma
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²)
open import DeloopS3.Cover.Orientation.CircleModel
  using (S¹≃C; circleToC; CToCircle; circle-section; circle-retraction; hC)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus

module LoopWords {ℓ : Level} {X : Type ℓ} {a : X}
  (j r : a ≡ a) (κ : j ∙ r ≡ sym r ∙ j) where

  -- Multiplying κ on either side; no group-presentation quotient.
  inverse-fibre : j ∙ sym r ≡ r ∙ j
  inverse-fibre =
    rUnit (j ∙ sym r)
    ∙ cong ((j ∙ sym r) ∙_) (sym (lCancel j))
    ∙ assoc (j ∙ sym r) (sym j) j
    ∙ cong (_∙ j) (sym (assoc j (sym r) (sym j)))
    ∙ cong (λ w → (j ∙ w) ∙ j)
        (sym (symDistr j r) ∙ cong sym κ ∙ symDistr (sym r) j)
    ∙ cong (_∙ j)
        (assoc j (sym j) r ∙ cong (_∙ r) (rCancel j) ∙ sym (lUnit r))

  -- A shorter derivation of the same inverse-fibre identity by solving
  -- κ after whiskering is used below; its entire two-cell is retained.
  twice-commutes : (j ∙ j) ∙ r ≡ r ∙ (j ∙ j)
  twice-commutes = sym (assoc j j r)
    ∙ cong (j ∙_) κ
    ∙ assoc j (sym r) j
    ∙ cong (_∙ j) inverse-fibre
    ∙ sym (assoc r j j)

-- Based comparison is supplied on both generating edges. The square
-- case is filled only because the target is already a groupoid.
module Compare {ℓ : Level} {X : Type ℓ} (gpd : isGroupoid X)
  (f g : T² → X) (p : f (0C , 0C) ≡ g (0C , 0C))
  (u : PathP (λ i → f (hC i , 0C) ≡ g (hC i , 0C)) p p)
  (v : PathP (λ i → f (0C , hC i) ≡ g (0C , hC i)) p p) where

  hs : (s t : S¹) → f (circleToC s , circleToC t) ≡ g (circleToC s , circleToC t)
  hs base base = p
  hs (loop i) base = u i
  hs base (loop k) = v k
  hs (loop i) (loop k) = cube i k
    where
    cube : SquareP (λ i k → f (hC i , hC k) ≡ g (hC i , hC k)) v v u u
    cube = toPathP (isOfHLevelPathP' 1 (gpd _ _) _ _ _ _)

  abstract
    homotopy : f ≡ g
    homotopy = funExt λ { (a , b) →
      sym (cong f (ΣPathP (circle-retraction a , circle-retraction b)))
      ∙ hs (CToCircle a) (CToCircle b)
      ∙ cong g (ΣPathP (circle-retraction a , circle-retraction b)) }

-- The canonical double traversal: the square is precisely the two
-- successive monodromy comparisons in twice-commutes.
module Double = LoopWords j r κ

λ₂S : S¹ × S¹ → Kinv
λ₂S (base , base) = kbase
λ₂S (loop i , base) = (j ∙ j) i
λ₂S (base , loop k) = r k
λ₂S (loop i , loop k) = compPath→Square Double.twice-commutes i k

λ₂ : T² → Kinv
λ₂ (a , t) = λ₂S (CToCircle a , CToCircle t)

abstract
  λ₂-base : λ₂ (0C , 0C) ≡ kbase
  λ₂-base = refl

  λ₂-u : cong λ₂ (λ i → hC i , 0C) ≡ j ∙ j
  λ₂-u = cong (λ q → cong (λ s → λ₂S (s , base)) q)
    (λ k i → circle-section (loop i) k)

  λ₂-v : cong λ₂ (λ i → 0C , hC i) ≡ r
  λ₂-v = cong (λ q → cong (λ s → λ₂S (base , s)) q)
    (λ k i → circle-section (loop i) k)
