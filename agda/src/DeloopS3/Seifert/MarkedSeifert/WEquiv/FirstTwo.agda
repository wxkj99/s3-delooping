{-# OPTIONS --safe --cubical #-}

-- Actual identity-leg cancellations.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.FirstTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.Data.Int using (ℤ; pos; _-_)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition public
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Shapes

private
  module Prod = Product {ℓ = ℓ-zero} {A = Unit} {B = C} {C = C}
    wedgeLeg wedgeLeg C
  fill₂ : T² → C
  fill₂ = row (pos 1) (pos 2)
  module Both = FillBoth {ℓ = ℓ-zero} {H = Unit × C}
    {A = T²} {B = T²} {X = C} {Y = C}
    Prod.leftMap Prod.rightMap fill₂ fill₂

  productTriangle : (z : T² ⊎ T²)
    → Prod.productPushout .fst (left12 z) ≡ Both.S.allLeft z
  productTriangle (left (a , t)) = Prod.product-left a t
  productTriangle (right (a , t)) = Prod.product-right a t

  abstract
    torusDiagram : FirstTwoFillings ≃ Both.S.All
    torusDiagram = pushoutEquiv left12 (right12 (pos 2) (pos 2))
      Both.S.allLeft Both.S.allRight (idEquiv (T² ⊎ T²))
      Prod.productPushout (idEquiv (C ⊎ C)) (funExt productTriangle)
      (funExt λ { (left z) → refl ; (right z) → refl })

    removeUnit : (Unit × C) ≃ C
    removeUnit = isoToEquiv (iso snd (tt ,_) (λ _ → refl) (λ { (tt , t) → refl }))

    commonCircle : Pushout (fill₂ ∘ Prod.leftMap) (fill₂ ∘ Prod.rightMap) ≃ W
    commonCircle = pushoutEquiv (fill₂ ∘ Prod.leftMap) (fill₂ ∘ Prod.rightMap)
      (mulC (pos 2)) (mulC (pos 2)) removeUnit (idEquiv C) (idEquiv C)
      refl refl

abstract
  firstTwoR1 : FirstTwoFillings ≃ W
  firstTwoR1 = compEquiv torusDiagram (compEquiv Both.fillBoth commonCircle)

-- Constructorwise form of the identity-leg contractions. Keeping this
-- map explicit makes the third boundary markings compute without
-- unfolding the composite span equivalences above.
coreMap : Core → W
coreMap (inl a , t) = inl (fill₂ (a , t))
coreMap (inr a , t) = inr (fill₂ (a , t))
coreMap (push tt i , t) = push t i

firstTwoMap : FirstTwoFillings → W
firstTwoMap (inl z) = coreMap z
firstTwoMap (inr (left z)) = inl z
firstTwoMap (inr (right z)) = inr z
firstTwoMap (push (left z) i) = inl (fill₂ z)
firstTwoMap (push (right z) i) = inr (fill₂ z)

private
  coreInc : Core → FirstTwoFillings
  coreInc = inl
  seamA : (z : T²) → coreInc (boundary₁ z) ≡ inr (left (fill₂ z))
  seamA z = push (left z)
  seamB : (z : T²) → coreInc (boundary₂ z) ≡ inr (right (fill₂ z))
  seamB z = push (right z)
  centralSeam : (t : C)
    → coreInc (inl 0C , t) ≡ coreInc (inr 0C , t)
  centralSeam t i = coreInc (push tt i , t)

  firstTwoInverse : W → FirstTwoFillings
  firstTwoInverse (inl z) = inr (left z)
  firstTwoInverse (inr z) = inr (right z)
  firstTwoInverse (push t i) =
    (sym (seamA (0C , t)) ∙∙ centralSeam t ∙∙ seamB (0C , t)) i

  firstTwoSec : (z : W) → firstTwoMap (firstTwoInverse z) ≡ z
  firstTwoSec (inl z) = refl
  firstTwoSec (inr z) = refl
  firstTwoSec (push t i) k =
    (cong-∙∙ firstTwoMap (sym (seamA (0C , t))) (centralSeam t) (seamB (0C , t))
      ∙ (λ k → doubleCompPath-filler refl (push t) refl (~ k))) k i

  coreRet : (z : Core) → firstTwoInverse (coreMap z) ≡ coreInc z
  coreRet (inl a , t) = sym (seamA (a , t))
  coreRet (inr a , t) = sym (seamB (a , t))
  coreRet (push tt i , t) k = doubleCompPath-filler
    (sym (seamA (0C , t))) (centralSeam t) (seamB (0C , t)) (~ k) i

  firstTwoRet : (z : FirstTwoFillings) → firstTwoInverse (firstTwoMap z) ≡ z
  firstTwoRet (inl z) = coreRet z
  firstTwoRet (inr (left z)) = refl
  firstTwoRet (inr (right z)) = refl
  firstTwoRet (push (left z) i) k = seamA z (i ∨ ~ k)
  firstTwoRet (push (right z) i) k = seamB z (i ∨ ~ k)

abstract
  firstTwo : FirstTwoFillings ≃ W
  firstTwo = isoToEquiv (iso firstTwoMap firstTwoInverse firstTwoSec firstTwoRet)
  firstTwo-map : firstTwo .fst ≡ firstTwoMap
  firstTwo-map = refl

-- The third map is transported as a function on the ENTIRE torus.
-- Its square is not reconstructed from two fundamental-group elements.
bW : T² → W
bW = coreMap ∘ boundary₃

bW-marked : firstTwo .fst ∘ thirdOriginal ≡ bW
bW-marked i t = firstTwo-map i (thirdOriginal t)

abstract
  thirdStaged : (e : ℤ) → M22e e ≃ Pushout bW (row (pos 1 - e) e)
  thirdStaged e = compEquiv (Seifert.S.stage₂ (pos 2) (pos 2) e)
    (pushoutEquiv thirdOriginal (row (pos 1 - e) e)
      bW (row (pos 1 - e) e) (idEquiv T²) firstTwo (idEquiv C) bW-marked refl)

-- Exact transported base, loops and product square, before word simplification.
bW-base : W
bW-base = bW (0C , 0C)

bW-u bW-v : bW-base ≡ bW-base
bW-u = cong bW (λ i → hC i , 0C)
bW-v = cong bW (λ i → 0C , hC i)

bW-square : PathP (λ i → bW-u i ≡ bW-u i) bW-v bW-v
bW-square i j = bW (hC i , hC j)
