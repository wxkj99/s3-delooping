{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The actual inversion family and its total space.
-- The library's untruncated Klein HIT has precisely the naturality square.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos; -Involutive)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emsquash; emloop-sym)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.HITs.S1.Base
open import Cubical.HITs.S1.Properties using (isGroupoidS¹)
import Cubical.HITs.KleinBottle.Base as KB
import Cubical.HITs.KleinBottle.Properties as KP
open import DeloopS3.Move.CancelMinimal using (C; 0C; ua-equiv-family)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C; circleToC; hC)
open import DeloopS3.Seifert.TwistedBundle.SignCircle using (negC)

abstract
  negC-invol : (t : C) → negC (negC t) ≡ t
  negC-invol = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ n i k → emloop (-Involutive n k) i)

  ι : C ≃ C
  ι = isoToEquiv (iso negC negC negC-invol negC-invol)

  ι-map : ι .fst ≡ negC
  ι-map = refl

  ι-base : ι .fst 0C ≡ 0C
  ι-base = refl

  ι-square : (t : C) → ι .fst (ι .fst t) ≡ t
  ι-square = negC-invol

  ι-square-base : ι-square 0C ≡ cong (ι .fst) ι-base ∙ ι-base
  ι-square-base = rUnit refl

  ι² : compEquiv ι ι ≡ idEquiv C
  ι² = equivEq (funExt ι-square)

  ι-loop : PathP (λ k → ι-base k ≡ ι-base k)
    (cong (ι .fst) hC) (sym hC)
  ι-loop k i = emloop-sym ℤGroup (pos 1) k i

Dinv : S¹ → Type₀
Dinv base = C
Dinv (loop i) = ua ι i

Kinv : Type₀
Kinv = Σ S¹ Dinv

-- Pointed circle chart intertwines the two actual inversion maps.
abstract
  chart-inversion : (t : S¹) → negC (circleToC t) ≡ circleToC (invLooper t)
  chart-inversion base = refl
  chart-inversion (loop i) k = emloop-sym ℤGroup (pos 1) k i

  circleFamilyChart : (b : S¹) → KP.invS¹Loop b ≃ Dinv b
  circleFamilyChart base = S¹≃C
  circleFamilyChart (loop i) = ua-equiv-family invS¹Equiv (λ k → ua ι k)
    S¹≃C S¹≃C
    (λ t → ua-gluePath ι
      (cong (λ f → f (circleToC t)) ι-map ∙ chart-inversion t)) i

abstract
  -- An equivalence with the actual Σ-family; no Bπ₁ replacement occurs.
  klein≃Kinv : KB.KleinBottle ≃ Kinv
  klein≃Kinv = compEquiv KP.kleinBottle≃Σ (Σ-cong-equiv-snd circleFamilyChart)

  klein-base : klein≃Kinv .fst KB.point ≡ (base , 0C)
  klein-base = refl

kbase : Kinv
kbase = klein≃Kinv .fst KB.point

j r : kbase ≡ kbase
j = cong (klein≃Kinv .fst) KB.line2
r = cong (klein≃Kinv .fst) KB.line1

κ : j ∙ r ≡ sym r ∙ j
κ = sym (Square→compPath (λ i k → klein≃Kinv .fst (KB.square i k)))

fibre : C → Kinv
fibre t = base , t

abstract
  -- These paths retain the basepoint change in the chosen total chart.
  r-as-fibre : r ≡ (klein-base ∙ cong fibre hC) ∙ sym klein-base
  r-as-fibre = lUnit r ∙ rUnit (refl ∙ r)

  j-baseProjection :
    (sym (cong fst klein-base) ∙ cong fst j) ∙ cong fst klein-base ≡ sym loop
  j-baseProjection = cong (_∙ refl) (sym (lUnit (sym loop)))
    ∙ sym (rUnit (sym loop))

  r-baseProjection :
    (sym (cong fst klein-base) ∙ cong fst r) ∙ cong fst klein-base ≡ refl
  r-baseProjection = cong (_∙ refl) (sym (lUnit refl)) ∙ sym (rUnit refl)

-- Groupoidness is derived from the actual circle family, after its HIT
-- identification; it is not an assumption in the preceding equivalence.
Dinv-groupoid : (b : S¹) → isGroupoid (Dinv b)
Dinv-groupoid base = emsquash
Dinv-groupoid (loop i) = isProp→PathP
  (λ k → isPropIsOfHLevel {A = Dinv (loop k)} 3) emsquash emsquash i

abstract
  isGroupoidKinv : isGroupoid Kinv
  isGroupoidKinv = isOfHLevelΣ 3 isGroupoidS¹ Dinv-groupoid
