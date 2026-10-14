{-# OPTIONS --safe --cubical #-}

-- The actual torus coordinate change.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Int as Z using (ℤ; pos)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup; ℤHom)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emsquash)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
  using (assocₖ; commₖ; -ₖ_; rCancelₖ; lCancelₖ; rUnitₖ; lUnitₖ)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC; _+C_)
open import DeloopS3.Move.CancelGeneral using (module CircleCoordinates)
open import DeloopS3.Move.ShearFormula using (TκEquiv; module ClassifyingAddition)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)

abstract
  mulC-one : (a : C) → mulC (pos 1) a ≡ a
  mulC-one = elimSet ℤGroup (λ _ → emsquash _ _) refl (λ n i j → emloop n i)

  mulC-pres+ : (e : ℤ) (a b : C)
    → mulC e (a +C b) ≡ mulC e a +C mulC e b
  mulC-pres+ e = ClassifyingAddition.B-pres+ {G = ℤAbGroup} {H = ℤAbGroup} (ℤHom e)

swap : T² → T²
swap (a , t) = t , a

σ : T² → T²
σ (u , v) = v , u +C v

abstract
  swapEquiv : T² ≃ T²
  swapEquiv = isoToEquiv (iso swap swap (λ _ → refl) (λ _ → refl))

  -- Literal swap followed by the shear, normalized at mulC 1.
  σEquiv : T² ≃ T²
  σEquiv = σ , subst isEquiv normalize (compEquiv swapEquiv (TκEquiv (pos 1)) .snd)
    where
    normalize : compEquiv swapEquiv (TκEquiv (pos 1)) .fst ≡ σ
    normalize = funExt λ { (u , v) → ΣPathP (refl , cong (u +C_) (mulC-one v)) }

  σEquiv-map : σEquiv .fst ≡ σ
  σEquiv-map = refl

  coefficient : (e : ℤ) → (pos 1 Z.- e) Z.+ e ≡ pos 1
  coefficient e = sym (Z.+Assoc (pos 1) (Z.- e) e)
    ∙ cong (pos 1 Z.+_) (Z.-Cancel' e)

  rightBasis-point : (e : ℤ) (t : T²)
    → row (pos 1 Z.- e) e (σ t) ≡ row e (pos 1) t
  rightBasis-point e (u , v) =
    cong (mulC (pos 1 Z.- e) v +C_) (mulC-pres+ e u v)
    ∙ assocₖ {G = ℤAbGroup} 1 (mulC (pos 1 Z.- e) v) (mulC e u) (mulC e v)
    ∙ cong (_+C mulC e v)
        (commₖ {G = ℤAbGroup} 1 (mulC (pos 1 Z.- e) v) (mulC e u))
    ∙ sym (assocₖ {G = ℤAbGroup} 1 (mulC e u) (mulC (pos 1 Z.- e) v) (mulC e v))
    ∙ cong (mulC e u +C_)
        (sym (CircleCoordinates.mulC-add (pos 1 Z.- e) e v)
          ∙ cong (λ n → mulC n v) (coefficient e))

  rightBasis : (e : ℤ) → row (pos 1 Z.- e) e ∘ σ ≡ row e (pos 1)
  rightBasis e = funExt (rightBasis-point e)

σ⁻¹ : T² → T²
σ⁻¹ (a , t) = t +C (-ₖ_ {G = ℤAbGroup} {n = 1} a) , a

abstract
  σ-section : (x : T²) → σ (σ⁻¹ x) ≡ x
  σ-section (a , t) = ΣPathP (refl ,
    (sym (assocₖ {G = ℤAbGroup} 1 t (-ₖ_ {G = ℤAbGroup} {n = 1} a) a)
      ∙ cong (t +C_) (lCancelₖ {G = ℤAbGroup} 1 a)
      ∙ rUnitₖ {G = ℤAbGroup} 1 t))

  σ-retraction : (x : T²) → σ⁻¹ (σ x) ≡ x
  σ-retraction (u , v) = ΣPathP
    ((sym (assocₖ {G = ℤAbGroup} 1 u v (-ₖ_ {G = ℤAbGroup} {n = 1} v))
      ∙ cong (u +C_) (rCancelₖ {G = ℤAbGroup} 1 v)
      ∙ rUnitₖ {G = ℤAbGroup} 1 u) , refl)

  σEquiv-inverse : invEq σEquiv ≡ σ⁻¹
  σEquiv-inverse = funExt λ x →
    cong (invEq σEquiv)
      (sym (σ-section x) ∙ sym (cong (λ f → f (σ⁻¹ x)) σEquiv-map))
      ∙ retEq σEquiv (σ⁻¹ x)
