{-# OPTIONS --safe --cubical #-}

-- Boundary calculations as actual based loops.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Boundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos; ·IdL)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emsquash; emloop-comp)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (rUnitₖ)
open import DeloopS3.Move.CancelMinimal using (C; 0C; mulC)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Cover.Orientation.CircleModel using (hC; CToCircle)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.FirstTwo
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge using (LoopSquare)

w₀ : W
w₀ = inl 0C

leftCircle rightCircle : C → W
leftCircle = inl
rightCircle = inr

connecting : leftCircle 0C ≡ rightCircle 0C
connecting = push 0C

xW yW : w₀ ≡ w₀
xW = cong leftCircle hC
yW = (connecting ∙ cong rightCircle hC) ∙ sym connecting

private
  core₀ : P → W
  core₀ z = coreMap (z , 0C)
  meridian : C → C
  meridian a = row (pos 1) (pos 2) (a , 0C)
  mul-one : (a : C) → mulC (pos 1) a ≡ a
  mul-one = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ g i k → emloop (·IdL g k) i)
  meridian-id : (a : C) → meridian a ≡ a
  meridian-id a = rUnitₖ {G = ℤAbGroup} 1 (mulC (pos 1) a) ∙ mul-one a
  meridian-loop : cong meridian hC ≡ hC
  meridian-loop = (λ k i → rUnitₖ {G = ℤAbGroup} 1 (mulC (pos 1) (hC i)) k)
    ∙ (λ k i → mul-one (hC i) k)

  core-a : cong core₀ a ≡ xW
  core-a = cong (cong leftCircle) meridian-loop
  core-b : cong core₀ b ≡ yW
  core-b = cong-∙ core₀ (edge ∙ cong d₂ hC) (sym edge)
    ∙ cong (_∙ sym connecting) (cong-∙ core₀ edge (cong d₂ hC))
    ∙ cong (λ p → (connecting ∙ p) ∙ sym connecting)
      (cong (cong rightCircle) meridian-loop)

  d₃-positive : cong d₃ hC ≡ sym (a ∙ b)
  d₃-positive = cong (cong (circleMap (sym (a ∙ b)))) (sym (lUnit loop))

-- No truncations: these are equalities in the loop space of W itself.
boundary-meridian : bW-u ≡ sym (xW ∙ yW)
boundary-meridian = cong (cong core₀) d₃-positive
  ∙ cong sym (cong-∙ core₀ a b ∙ cong₂ _∙_ core-a core-b)

boundary-fibre-x : bW-v ≡ xW ∙ xW
boundary-fibre-x = cong (cong leftCircle) (emloop-comp ℤGroup (pos 1) (pos 1))
  ∙ cong-∙ leftCircle hC hC

private
  rightFibre : rightCircle 0C ≡ rightCircle 0C
  rightFibre = cong (rightCircle ∘ mulC (pos 2)) hC
  rightFibre-square : rightFibre ≡ cong rightCircle hC ∙ cong rightCircle hC
  rightFibre-square = cong (cong rightCircle) (emloop-comp ℤGroup (pos 1) (pos 1))
    ∙ cong-∙ rightCircle hC hC
  commonSquare : LoopSquare bW-v rightFibre connecting
  commonSquare i k = push (hC i) k

-- Singleton elimination, retaining the supplied square, not a filler.
squareToConjugate : {ℓ : Level} {X : Type ℓ} {a b : X}
  (p : a ≡ a) (γ : a ≡ b) (q : b ≡ b)
  → LoopSquare p q γ → p ≡ (γ ∙ q) ∙ sym γ
squareToConjugate {a = a} p γ = J
  (λ b γ → (q : b ≡ b) → LoopSquare p q γ → p ≡ (γ ∙ q) ∙ sym γ)
  (λ q s → (λ k i → s i k) ∙ lUnit q ∙ rUnit (refl ∙ q)) γ

conjugateSquare : {ℓ : Level} {X : Type ℓ} {a b : X}
  (γ : a ≡ b) (q : b ≡ b)
  → (γ ∙ (q ∙ q)) ∙ sym γ ≡ ((γ ∙ q) ∙ sym γ) ∙ ((γ ∙ q) ∙ sym γ)
conjugateSquare {a = a} γ = J
  (λ b γ → (q : b ≡ b) → (γ ∙ (q ∙ q)) ∙ sym γ
    ≡ ((γ ∙ q) ∙ sym γ) ∙ ((γ ∙ q) ∙ sym γ))
  (λ q → sym (rUnit (refl ∙ (q ∙ q))) ∙ sym (lUnit (q ∙ q))
    ∙ cong₂ _∙_ (lUnit q ∙ rUnit (refl ∙ q)) (lUnit q ∙ rUnit (refl ∙ q))) γ

boundary-fibre-y : bW-v ≡ yW ∙ yW
boundary-fibre-y = squareToConjugate bW-v connecting rightFibre commonSquare
  ∙ cong (λ p → (connecting ∙ p) ∙ sym connecting) rightFibre-square
  ∙ conjugateSquare connecting (cong rightCircle hC)

W-relation : xW ∙ xW ≡ yW ∙ yW
W-relation = sym boundary-fibre-x ∙ boundary-fibre-y
