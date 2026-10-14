{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.CellLabels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙ ; cong-∙)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.Sn using (S₊ ; ptSn)
open import DeloopS3.Bridge.CellularPushout.CellGroups

-- A characteristic sphere written using its cap and spoke paths.  This
-- keeps naturality independent of the section proof chosen for a chart.
open import Cubical.HITs.S1 using (base ; loop)
open import Cubical.HITs.Susp using (north ; south ; merid)
open import Cubical.Data.Bool using (false)

cellSphere : (d : ℕ) {Q : Type} (z : Q)
  (ends : S₊ d → Q) (center : Q)
  (caps : (s : S₊ d) → z ≡ ends s)
  (spokes : (s : S₊ d) → ends s ≡ center) → S₊ (suc d) → Q
cellSphere zero z ends center caps spokes base = z
cellSphere zero z ends center caps spokes (loop i) =
  (caps false ∙∙ (spokes false ∙ sym (spokes (ptSn zero))) ∙∙ sym (caps (ptSn zero))) i
cellSphere (suc d) z ends center caps spokes north = z
cellSphere (suc d) z ends center caps spokes south = z
cellSphere (suc d) z ends center caps spokes (merid s i) =
  (caps s ∙∙ (spokes s ∙ sym (spokes (ptSn (suc d)))) ∙∙ sym (caps (ptSn (suc d)))) i

abstract
  cellLoop-map : {Q R : Type} (f : Q → R) {z x y c : Q}
    (u : z ≡ x) (p : x ≡ c) (q : y ≡ c) (v : z ≡ y)
    → cong f (u ∙∙ (p ∙ sym q) ∙∙ sym v)
     ≡ (cong f u ∙∙ (cong f p ∙ sym (cong f q)) ∙∙ sym (cong f v))
  cellLoop-map f u p q v = cong-∙∙ f u (p ∙ sym q) (sym v)
    ∙ cong (λ r → cong f u ∙∙ r ∙∙ sym (cong f v)) (cong-∙ f p (sym q))

  cellSphere-map : (d : ℕ) {Q R : Type} (f : Q → R) (z : Q)
    (ends : S₊ d → Q) (center : Q)
    (caps : (s : S₊ d) → z ≡ ends s)
    (spokes : (s : S₊ d) → ends s ≡ center)
    → f ∘ cellSphere d z ends center caps spokes
     ≡ cellSphere d (f z) (f ∘ ends) (f center)
         (λ s → cong f (caps s)) (λ s → cong f (spokes s))
  cellSphere-map zero f z ends center caps spokes = funExt
    λ { base → refl
      ; (loop i) j → cellLoop-map f (caps false) (spokes false)
          (spokes (ptSn zero)) (caps (ptSn zero)) j i }
  cellSphere-map (suc d) f z ends center caps spokes = funExt
    λ { north → refl ; south → refl
      ; (merid s i) j → cellLoop-map f (caps s) (spokes s)
          (spokes (ptSn (suc d))) (caps (ptSn (suc d))) j i }

open import Cubical.Foundations.Equiv using (_≃_ ; invEq)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (preBTC)

abstract
  preBTC-cellSphere : (d m : ℕ) {X Y : Type}
    (α : Fin m × S₊ d → X) (e : Y ≃ Pushout α fst) (a : Fin m)
    → fst (preBTC (suc d) m α e a)
     ≡ cellSphere d (inl _)
         (λ s → inr (invEq e (inl (α (a , s))))) (inr (invEq e (inr a)))
         (λ s → push (α (a , s))) (λ s → cong {B = λ _ → cofib (invEq e ∘ inl)} (λ x → inr (invEq e x)) (push (a , s)))
  preBTC-cellSphere zero m α e a = funExt
    λ { base → refl
      ; (loop i) j → cong
          (λ p → push (α (a , false)) ∙∙ p ∙∙ sym (push (α (a , ptSn zero))))
          (cong-∙ {B = cofib (invEq e ∘ inl)} (λ x → inr (invEq e x)) (push (a , false)) (sym (push (a , ptSn zero)))) j i }
  preBTC-cellSphere (suc d) m α e a = funExt
    λ { north → refl ; south → refl
      ; (merid s i) j → cong
          (λ p → push (α (a , s)) ∙∙ p ∙∙ sym (push (α (a , ptSn (suc d)))))
          (cong-∙ {B = cofib (invEq e ∘ inl)} (λ x → inr (invEq e x)) (push (a , s)) (sym (push (a , ptSn (suc d))))) j i }

open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤFinFunct ; ℤFinGenerator ; agreeOnℤFinGenerator→≡ ; isGeneratorℤFinGenerator')
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree ; pickPetal)
open import Cubical.HITs.Sn.Degree using (degree)

abstract
  petalwise-degree : {d n m : ℕ} (κ : Fin n → Fin m)
    (F : SphereBouquet d (Fin n) → SphereBouquet d (Fin m))
    (onPetals : (a : Fin n) → (λ (s : S₊ d) → F (inr (a , s))) ≡ (λ s → inr (κ a , s)))
    → bouquetDegree F ≡ ℤFinFunct κ
  petalwise-degree {d} κ F onPetals = agreeOnℤFinGenerator→≡ λ a → funExt λ b →
    sym (isGeneratorℤFinGenerator' (λ t → degree d (λ s → pickPetal b (F (inr (t , s))))) a)
    ∙ cong (λ h → degree d (pickPetal b ∘ h)) (onPetals a)
    ∙ petal-degree d (κ a) b
    ∙ sym (cong (λ z → z b) (label-generator κ a))
