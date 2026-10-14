{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Model.OriginalGraph where

-- Comparison of rose coordinates with Definition.agda's literal wedge.
-- This is an equivalence of untruncated HITs, not a pi_1 argument.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Original
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Cert.Input.Model.Vocabulary using (Γ; twoGenerators)

originalToRose : Original.P → Γ
originalToRose (inl u) = R.circleRec R.root (R.petal fzero) (Circle.CToCircle u)
originalToRose (inr u) = R.circleRec R.root (R.petal (fsuc fzero)) (Circle.CToCircle u)
originalToRose (push tt i) = R.root

roseToOriginal : Γ → Original.P
roseToOriginal R.root = Original.p₀
roseToOriginal (R.petal fzero i) = Original.a i
roseToOriginal (R.petal (fsuc fzero) i) = Original.b i
roseToOriginal (R.petal (fsuc (fsuc ())) i)

abstract
  originalToRose-a : cong originalToRose Original.a ≡ R.petal fzero
  originalToRose-a = cong (cong (R.circleRec R.root (R.petal fzero))) (sym (lUnit loop))
  originalToRose-d₂ : cong (λ u → originalToRose (Original.d₂ u)) Circle.hC ≡ R.petal (fsuc fzero)
  originalToRose-d₂ = cong (cong (R.circleRec R.root (R.petal (fsuc fzero)))) (sym (lUnit loop))
  originalToRose-b : cong originalToRose Original.b ≡ R.petal (fsuc fzero)
  originalToRose-b = cong-∙ originalToRose (Original.edge ∙ cong Original.d₂ Circle.hC) (sym Original.edge)
    ∙ cong (_∙ refl) (cong-∙ originalToRose Original.edge (cong Original.d₂ Circle.hC)
      ∙ cong (refl ∙_) originalToRose-d₂ ∙ sym (lUnit (R.petal (fsuc fzero))))
    ∙ sym (rUnit (R.petal (fsuc fzero)))

rose-unit : (x : Γ) → originalToRose (roseToOriginal x) ≡ x
rose-unit R.root = refl
rose-unit (R.petal fzero i) j = originalToRose-a j i
rose-unit (R.petal (fsuc fzero) i) j = originalToRose-b j i
rose-unit (R.petal (fsuc (fsuc ())) i)

private
  left-circle : (u : S¹) → roseToOriginal (R.circleRec R.root (R.petal fzero) u)
    ≡ Original.d₁ (Circle.circleToC u)
  left-circle base = refl
  left-circle (loop i) = refl

  right-loop : Original.b ∙ Original.edge ≡ Original.edge ∙ cong Original.d₂ Circle.hC
  right-loop = sym (assoc (Original.edge ∙ cong Original.d₂ Circle.hC) (sym Original.edge) Original.edge)
    ∙ cong ((Original.edge ∙ cong Original.d₂ Circle.hC) ∙_) (lCancel Original.edge)
    ∙ sym (rUnit (Original.edge ∙ cong Original.d₂ Circle.hC))

  right-circle : (u : S¹) → roseToOriginal (R.circleRec R.root (R.petal (fsuc fzero)) u)
    ≡ Original.d₂ (Circle.circleToC u)
  right-circle base = Original.edge
  right-circle (loop i) j = compPath→Square right-loop i j

  left-counit : (u : R.C) → roseToOriginal (originalToRose (inl u)) ≡ inl u
  left-counit u = left-circle (Circle.CToCircle u) ∙ cong inl (Circle.circle-retraction u)
  right-counit : (u : R.C) → roseToOriginal (originalToRose (inr u)) ≡ inr u
  right-counit u = right-circle (Circle.CToCircle u) ∙ cong inr (Circle.circle-retraction u)

  edge-counit : PathP (λ i → Original.p₀ ≡ Original.edge i)
    (left-counit R.0C) (right-counit R.0C)
  edge-counit = subst2 (λ p q → PathP (λ i → Original.p₀ ≡ Original.edge i) p q)
    (rUnit refl) (rUnit Original.edge) (λ i j → Original.edge (i ∧ j))

original-counit : (x : Original.P) → roseToOriginal (originalToRose x) ≡ x
original-counit (inl u) = left-counit u
original-counit (inr u) = right-counit u
original-counit (push tt i) = edge-counit i

originalGraphEquiv : Original.P ≃ Γ
originalGraphEquiv = isoToEquiv (iso originalToRose roseToOriginal rose-unit original-counit)

originalAttach : Ch.Kind → R.C → Original.P
originalAttach Ch.A = Original.d₁
originalAttach Ch.B = Original.d₂
originalAttach Ch.C = Original.d₃

abstract
  original-third-word : cong originalToRose (sym (Original.a ∙ Original.b))
    ≡ R.roseWord twoGenerators (Ch.kindWord Ch.C)
  original-third-word = cong sym (cong-∙ originalToRose Original.a Original.b
      ∙ cong₂ _∙_ originalToRose-a originalToRose-b)
    ∙ symDistr (R.petal fzero) (R.petal (fsuc fzero))
    ∙ cong (sym (R.petal (fsuc fzero)) ∙_) (rUnit (sym (R.petal fzero)))

private
  third-circle : (u : S¹) → originalToRose (circleMap (sym (Original.a ∙ Original.b)) u)
    ≡ R.circleRec R.root (R.roseWord twoGenerators (Ch.kindWord Ch.C)) u
  third-circle base = refl
  third-circle (loop i) j = original-third-word j i

original-boundary-square : (k : Ch.Kind) (u : R.C)
  → originalToRose (originalAttach k u) ≡ R.wordCircle twoGenerators (Ch.kindWord k) u
original-boundary-square Ch.A u = cong (λ p → R.circleRec R.root p (Circle.CToCircle u)) (rUnit (R.petal fzero))
original-boundary-square Ch.B u = cong (λ p → R.circleRec R.root p (Circle.CToCircle u)) (rUnit (R.petal (fsuc fzero)))
original-boundary-square Ch.C u = third-circle (Circle.CToCircle u)

originalAttach-base : (k : Ch.Kind) → originalToRose (originalAttach k R.0C) ≡ R.root
originalAttach-base Ch.A = refl
originalAttach-base Ch.B = refl
originalAttach-base Ch.C = refl

original-boundary-base : (k : Ch.Kind) → original-boundary-square k R.0C ≡ originalAttach-base k
original-boundary-base Ch.A = refl
original-boundary-base Ch.B = refl
original-boundary-base Ch.C = refl
