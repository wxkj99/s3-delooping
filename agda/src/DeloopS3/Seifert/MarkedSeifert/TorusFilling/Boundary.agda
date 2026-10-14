{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Based edge calculations and the full cube.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.Sigma
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (rUnitₖ)
open import DeloopS3.Move.CancelMinimal using (C; T²; 0C; _+C_)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap

uT vT : Path T² (0C , 0C) (0C , 0C)
uT i = hC i , 0C
vT i = 0C , hC i

abstract
  σ-u : cong σ uT ≡ vT
  σ-u k i = 0C , rUnitₖ {G = ℤAbGroup} 1 (hC i) k

  σ-v : cong σ vT ≡ uT ∙ vT
  σ-v = cong₂Funct {A = C} {B = T²} _,_ hC hC

based : {ℓ : Level} {X : Type ℓ} {a b : X}
  → a ≡ b → a ≡ a → b ≡ b
based p l = (sym p ∙ l) ∙ p

abstract
  based-refl : {ℓ : Level} {X : Type ℓ} {a : X} (l : a ≡ a)
    → based refl l ≡ l
  based-refl l = cong (_∙ refl) (sym (lUnit l)) ∙ sym (rUnit l)

  based-comp : {ℓ : Level} {X : Type ℓ} {a b : X}
    (p : a ≡ b) (l m : a ≡ a)
    → based p (l ∙ m) ≡ based p l ∙ based p m
  based-comp {a = a} p l m = J
    (λ b p → based p (l ∙ m) ≡ based p l ∙ based p m)
    (based-refl (l ∙ m)
      ∙ cong₂ _∙_ (sym (based-refl l)) (sym (based-refl m))) p

  based-square : {ℓ : Level} {X : Type ℓ} {a b : X}
    (p : a ≡ b) (l : a ≡ a) (k : b ≡ b)
    → based p l ≡ k → Square p p l k
  based-square p l k q = compPath→Square
    (sym (assoc p (sym p ∙ l) p
      ∙ cong (_∙ p)
        (assoc p (sym p) l ∙ cong (_∙ l) (rCancel p) ∙ sym (lUnit l)))
      ∙ cong (p ∙_) q)

  -- (xy)⁻¹ h = r, with y = j r⁻¹ and h = j².
  old-meridian-fibre : sym (j ∙ (j ∙ sym r)) ∙ (j ∙ j) ≡ r
  old-meridian-fibre = cong (_∙ (j ∙ j))
    (cong sym (assoc j j (sym r)) ∙ symDistr (j ∙ j) (sym r))
    ∙ sym (assoc r (sym (j ∙ j)) (j ∙ j))
    ∙ cong (r ∙_) (lCancel (j ∙ j)) ∙ sym (rUnit r)

-- The hypotheses are exactly the retained based loop markings of bW,
-- after its comparison into the already identified mapping torus.
-- No hypothesis about the torus square is needed: Compare fills it in
-- the proven 1-type Kinv, not in W or in the untruncated relation HIT.
module MarkedBoundary
  (b : T² → Kinv) (p : b (0C , 0C) ≡ kbase)
  (bu : based p (cong b uT) ≡ sym (j ∙ (j ∙ sym r)))
  (bv : based p (cong b vT) ≡ j ∙ j) where

  abstract
    new-u : based p (cong (b ∘ σ) uT) ≡ j ∙ j
    new-u = cong (based p) (cong (cong b) σ-u) ∙ bv

    new-v : based p (cong (b ∘ σ) vT) ≡ r
    new-v = cong (based p)
      (cong (cong b) σ-v ∙ cong-∙ b uT vT)
      ∙ based-comp p (cong b uT) (cong b vT)
      ∙ cong₂ _∙_ bu bv ∙ old-meridian-fibre

    leftBasis : b ∘ σ ≡ λ₂
    leftBasis = Compare.homotopy isGroupoidKinv (b ∘ σ) λ₂ p
      (based-square p (cong (b ∘ σ) uT) (cong λ₂ uT) (new-u ∙ sym λ₂-u))
      (based-square p (cong (b ∘ σ) vT) (cong λ₂ vT) (new-v ∙ sym λ₂-v))
