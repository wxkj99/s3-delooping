{-# OPTIONS --safe --cubical #-}

-- The positive model adapter for oriented circle classification.
module DeloopS3.Cover.Orientation.CircleModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM₁
open import Cubical.HITs.S1.Base
open import Cubical.HITs.S1.Properties using (isGroupoidS¹)
open import DeloopS3.Move.CancelMinimal using (C; 0C)

hC : 0C ≡ 0C
hC = emloop (pos 1)

circleToC : S¹ → C
circleToC base = 0C
circleToC (loop i) = hC i

circleToC-loop : cong circleToC loop ≡ hC
circleToC-loop = refl

CToCircle : C → S¹
CToCircle = EM₁.rec' ℤGroup isGroupoidS¹ base intLoop
  (λ n m → sym (intLoop-hom n m))

circleToC-intLoop : (n : ℤ) → cong circleToC (intLoop n) ≡ emloop n
circleToC-intLoop (pos zero) = sym (emloop-1g ℤGroup)
circleToC-intLoop (pos (suc n)) = cong-∙ circleToC (intLoop (pos n)) loop
  ∙ cong (_∙ hC) (circleToC-intLoop (pos n))
  ∙ sym (emloop-comp ℤGroup (pos n) (pos 1))
circleToC-intLoop (negsuc zero) = sym (emloop-sym ℤGroup (pos 1))
circleToC-intLoop (negsuc (suc n)) =
  cong-∙ circleToC (intLoop (negsuc n)) (sym loop)
  ∙ cong₂ _∙_ (circleToC-intLoop (negsuc n))
      (sym (emloop-sym ℤGroup (pos 1)))
  ∙ sym (emloop-comp ℤGroup (negsuc n) (negsuc zero))

circle-section : (x : S¹) → CToCircle (circleToC x) ≡ x
circle-section base = refl
circle-section (loop i) j = lUnit loop (~ j) i

circle-retraction : (x : C) → circleToC (CToCircle x) ≡ x
circle-retraction = EM₁.elimSet ℤGroup (λ _ → emsquash _ _) refl
  (λ n i j → circleToC-intLoop n j i)

isEquiv-circleToC : isEquiv circleToC
isEquiv-circleToC = isoToIsEquiv
  (iso circleToC CToCircle circle-retraction circle-section)

S¹≃C : S¹ ≃ C
S¹≃C = circleToC , isEquiv-circleToC
