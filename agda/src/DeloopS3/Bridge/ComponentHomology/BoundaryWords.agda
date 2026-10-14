{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.BoundaryWords where

-- The literal Seifert words and their signed exponent vectors, evaluated
-- by bouquetDegree.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; ·IdR ; ·IdL)
import Cubical.Data.Int as Z
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop ; winding)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree)
open import Cubical.HITs.Sn.Degree using (degree)
open import DeloopS3.Move.CancelMinimal using (C)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-section ; circle-retraction ; hC)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as D
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre using (one-petal)

-- This is a concrete map on the actual wedge, with its joining edge
-- retained.  Its petal coordinates are exactly the two signed exponents.
word-chart : D.P → SphereBouquet 1 (Fin 2)
word-chart (inl x) = inr (fzero , CToCircle x)
word-chart (inr x) = inr (fsuc fzero , CToCircle x)
word-chart (push tt i) = (sym (push fzero) ∙ push (fsuc fzero)) i

private
  chart-inverse : SphereBouquet 1 (Fin 2) → D.P
  chart-inverse (inl tt) = D.p₀
  chart-inverse (inr ((0 , p) , x)) = D.d₁ (circleToC x)
  chart-inverse (inr ((1 , p) , x)) = D.d₂ (circleToC x)
  chart-inverse (push (0 , p) i) = D.p₀
  chart-inverse (push (1 , p) i) = D.edge i

  chart-section : (x : SphereBouquet 1 (Fin 2)) → word-chart (chart-inverse x) ≡ x
  chart-section (inl tt) = sym (push fzero)
  chart-section (inr ((0 , p) , x)) j = inr (fzero , circle-section x j)
  chart-section (inr ((1 , p) , x)) j = inr (fsuc fzero , circle-section x j)
  chart-section (push (0 , p) i) j = push fzero (i ∨ ~ j)
  chart-section (push (1 , p) i) j =
    compPath-filler' (sym (push fzero)) (push (fsuc fzero)) (~ j) i

  chart-retraction : (x : D.P) → chart-inverse (word-chart x) ≡ x
  chart-retraction (inl x) = cong D.d₁ (circle-retraction x)
  chart-retraction (inr x) = cong D.d₂ (circle-retraction x)
  chart-retraction (push tt i) j =
    (cong-∙ chart-inverse (sym (push fzero)) (push (fsuc fzero))
      ∙ sym (lUnit D.edge)) j i

abstract
  word-chart-equiv : D.P ≃ SphereBouquet 1 (Fin 2)
  word-chart-equiv = isoToEquiv (iso word-chart chart-inverse chart-section chart-retraction)

  word-chart-point : word-chart D.p₀ ≡ inl tt
  word-chart-point = sym (push fzero)

private
  πa πb : D.P → S¹
  πa = pickPetal fzero ∘ word-chart
  πb = pickPetal (fsuc fzero) ∘ word-chart

  abstract
    edge-a : cong πa D.edge ≡ refl
    edge-a = cong-∙ (pickPetal fzero) (sym (push fzero)) (push (fsuc fzero))
      ∙ sym (lUnit refl)

    edge-b : cong πb D.edge ≡ refl
    edge-b = cong-∙ (pickPetal (fsuc fzero)) (sym (push fzero)) (push (fsuc fzero))
      ∙ sym (lUnit refl)

    aa : cong πa D.a ≡ loop
    aa = λ j i → circle-section (loop i) j

    ba : cong πb D.a ≡ refl
    ba = refl

  conjugate-refl : {X : Type} {x : X} (p q : x ≡ x)
    → p ≡ refl → (p ∙ q) ∙ sym p ≡ q
  conjugate-refl p q e = cong (λ r → (r ∙ q) ∙ sym r) e
    ∙ cong (_∙ refl) (sym (lUnit q)) ∙ sym (rUnit q)

  abstract
    ab : cong πa D.b ≡ refl
    ab = cong-∙ πa (D.edge ∙ cong D.d₂ hC) (sym D.edge)
      ∙ cong (_∙ sym (cong πa D.edge)) (cong-∙ πa D.edge (cong D.d₂ hC))
      ∙ conjugate-refl (cong πa D.edge) refl edge-a

    bb : cong πb D.b ≡ loop
    bb = cong-∙ πb (D.edge ∙ cong D.d₂ hC) (sym D.edge)
      ∙ cong (_∙ sym (cong πb D.edge)) (cong-∙ πb D.edge (cong D.d₂ hC))
      ∙ conjugate-refl (cong πb D.edge) (cong CToCircle hC) edge-b
      ∙ (λ j i → circle-section (loop i) j)

  third-circle : D.d₃ ∘ circleToC ≡ circleMap (sym (D.a ∙ D.b))
  third-circle = funExt λ x → cong (circleMap (sym (D.a ∙ D.b))) (circle-section x)

abstract
  d₁-degree-a : degree 1 (πa ∘ D.d₁ ∘ circleToC) ≡ pos 1
  d₁-degree-a = cong (degree 1) (funExt circle-section)

  d₁-degree-b : degree 1 (πb ∘ D.d₁ ∘ circleToC) ≡ pos 0
  d₁-degree-b = refl

  d₂-degree-a : degree 1 (πa ∘ D.d₂ ∘ circleToC) ≡ pos 0
  d₂-degree-a = refl

  d₂-degree-b : degree 1 (πb ∘ D.d₂ ∘ circleToC) ≡ pos 1
  d₂-degree-b = cong (degree 1) (funExt circle-section)

  d₃-degree-a : degree 1 (πa ∘ D.d₃ ∘ circleToC) ≡ negsuc 0
  d₃-degree-a = cong (degree 1) (cong (πa ∘_) third-circle)
    ∙ cong winding (cong sym
      (cong-∙ πa D.a D.b ∙ cong₂ _∙_ aa ab ∙ sym (rUnit loop)))

  d₃-degree-b : degree 1 (πb ∘ D.d₃ ∘ circleToC) ≡ negsuc 0
  d₃-degree-b = cong (degree 1) (cong (πb ∘_) third-circle)
    ∙ cong winding (cong sym
      (cong-∙ πb D.a D.b ∙ cong₂ _∙_ ba bb ∙ sym (lUnit loop)))

word-bouquet : (C → D.P) → FinSphereBouquetMap 1 2 0
word-bouquet d = word-chart ∘ d ∘ circleToC ∘ one-petal

-- The unit circle generator maps to the signed exponent vector.  This
-- proves a degree statement about the maps, not a postulated matrix.
abstract
  boundary₁-exponents : fst (bouquetDegree (word-bouquet D.d₁)) (λ _ → pos 1)
    ≡ (λ { (0 , p) → pos 1 ; (1 , p) → pos 0 })
  boundary₁-exponents = funExt λ
    { (0 , p) → ·IdL _ ∙ d₁-degree-a
    ; (1 , p) → ·IdL _ ∙ d₁-degree-b }

  boundary₂-exponents : fst (bouquetDegree (word-bouquet D.d₂)) (λ _ → pos 1)
    ≡ (λ { (0 , p) → pos 0 ; (1 , p) → pos 1 })
  boundary₂-exponents = funExt λ
    { (0 , p) → ·IdL _ ∙ d₂-degree-a
    ; (1 , p) → ·IdL _ ∙ d₂-degree-b }

  boundary₃-exponents : fst (bouquetDegree (word-bouquet D.d₃)) (λ _ → pos 1)
    ≡ (λ _ → negsuc 0)
  boundary₃-exponents = funExt λ
    { (0 , p) → ·IdL _ ∙ d₃-degree-a
    ; (1 , p) → ·IdL _ ∙ d₃-degree-b }
