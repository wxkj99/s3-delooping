{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Derivative where

-- A finite square proof of the loop-power derivative.  Horizontal
-- composition of double loops becomes vertical composition by the two
-- unit homotopies; their values at refl agree.  Dependent composition
-- follows the recursion for Telescope.pow-refl.
open import DeloopS3.Local.Base using (powLoop)
open import DeloopS3.Local.Telescope using (pow-refl ; pow∙)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (Square≃doubleComp)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)

horizontal→vertical : {X : Pointed ℓ-zero} (q r : typ (Ω (Ω X)))
  → PathP (λ k → sym (lUnit (refl {x = pt X})) k ≡ sym (lUnit refl) k)
      (cong₂ _∙_ q r) (q ∙ r)
horizontal→vertical q r = cong₂Funct _∙_ q r ◁
  (λ k → cong (λ p → rUnit p (~ k)) q ∙ cong (λ p → lUnit p (~ k)) r)

power-square : (m : ℕ) (X : Pointed ℓ-zero) (q : typ (Ω (Ω X)))
  → PathP (λ k → pow-refl m X k ≡ pow-refl m X k)
      (cong (powLoop m) q) (powLoop m q)
power-square zero X q = refl
power-square (suc m) X q = compPathP' {B = λ p → p ≡ p}
  {p = cong (refl ∙_) (pow-refl m X)} {q = sym (lUnit refl)}
  (λ k i → q i ∙ power-square m X q k i)
  (horizontal→vertical q (powLoop m q))

loop-power-derivative : (m : ℕ) (X : Pointed ℓ-zero)
  → (q : typ (Ω (Ω X))) → fst (Ω→ (pow∙ m X)) q ≡ powLoop m q
loop-power-derivative m X q = equivFun
  (Square≃doubleComp (cong (powLoop m) q) (powLoop m q) (pow-refl m X) (pow-refl m X))
  (power-square m X q)
