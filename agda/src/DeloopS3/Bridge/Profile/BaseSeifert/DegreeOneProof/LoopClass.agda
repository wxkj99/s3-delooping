{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit ; rUnit)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (map-square)
open import DeloopS3.Move.CancelLoopCell using (circleMap)

-- The class is the actual cellular image of the oriented circle generator.
-- It is transparent and does not require connectedness.
loop-class : (X : CW₀) (x : fst X) → x ≡ x → fst (H̃ᶜʷ X 1)
loop-class X x p =
  fst (cellular-map (Sᶜʷ 1) X 1 (circleMap p)) (genHₙSⁿ 0)

private
  abstract
    circle-map-natural : (X Y : CW₀) (f : fst X → fst Y)
      (x : fst X) (p : x ≡ x)
      → f ∘ circleMap p ≡ circleMap (cong f p)
    circle-map-natural X Y f x p = funExt λ
      { base → refl
      ; (loop i) → refl }

abstract
  loop-natural : (X Y : CW₀) (f : fst X → fst Y)
    (x : fst X) (p : x ≡ x)
    → fst (cellular-map X Y 1 f) (loop-class X x p)
      ≡ loop-class Y (f x) (cong f p)
  loop-natural X Y f x p =
    map-square (Sᶜʷ 1) X Y 1 (circleMap p) f (circleMap (cong f p))
      (circle-map-natural X Y f x p) (genHₙSⁿ 0)

abstract
  -- Path induction retains the loop at the varying endpoint in its motive.
  -- Thus rebasing is independent of connectedness.
  loop-rebase : (X : CW₀) (x y : fst X) (e : x ≡ y) (p : y ≡ y)
    → loop-class X x ((e ∙ p) ∙ sym e) ≡ loop-class X y p
  loop-rebase X x y e = J
    (λ y e → (p : y ≡ y)
      → loop-class X x ((e ∙ p) ∙ sym e) ≡ loop-class X y p)
    (λ p → cong (loop-class X x)
      (cong (λ q → q ∙ refl) (sym (lUnit p)) ∙ sym (rUnit p))) e
