{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- A dependent definition on actual torsors,
-- not a recursor on a putative point/loop/square presentation of BC₂.
module DeloopS3.Seifert.TwistedBundle.Torsor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; false; true; not; _⊕_; ⊕-comm; ⊕-invol; isSetBool)
open import Cubical.Data.Int as Z using (ℤ; pos; _+_; -_; isSetℤ; -Involutive; -Dist+; +Assoc; +Comm; -Cancel)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom; GroupIso→GroupHom)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.RPn.Base using (2-EltType₀; Bool*; module ⊕*)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.EilenbergMacLane1.Base using (embase; emloop; emsquash)
import Cubical.HITs.EilenbergMacLane1.Properties as EM₁
open import Cubical.Homotopy.EilenbergMacLane.Base using (EM)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (Iso→EM₁Iso; inducedFun-EM₁)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (_+ₖ_; addIso)
open import DeloopS3.Move.CancelMinimal using (C; 0C; _+C_)
open import DeloopS3.Move.ShearFormula using (module ClassifyingAddition)

B : Type₁
B = 2-EltType₀

frame : (T : B) → fst T → fst T ≃ Bool
frame = ⊕*.Equivʳ

op : (T : B) → fst T → fst T
op T y = invEq (frame T y) true

abstract
  frame-self : (T : B) (y : fst T) → frame T y .fst y ≡ false
  frame-self T = ⊕*.elim T (λ X f → (y : X) → f y y ≡ false)
    (λ _ _ → isPropΠ λ _ → isSetBool _ _) (λ { false → refl ; true → refl })

  frame-op : (T : B) (y : fst T) → frame T y .fst (op T y) ≡ true
  frame-op T y = secEq (frame T y) true

  op-invol : (T : B) (y : fst T) → op T (op T y) ≡ y
  op-invol T y = invEq (congEquiv (frame T (op T y)))
    (frame-op T (op T y) ∙ sym (⊕*.comm T (op T y) y ∙ frame-op T y))

  -- The change-of-frame equation is a proposition, so the library's
  -- finite-torsor eliminator applies, including to all higher paths in B.
  frame-compose : (T : B) (a b c : fst T)
    → frame T a .fst c ≡ frame T a .fst b ⊕ frame T b .fst c
  frame-compose T = ⊕*.elim T
    (λ X f → (a b c : X) → f a c ≡ f a b ⊕ f b c)
    (λ _ _ → isPropΠ3 λ _ _ _ → isSetBool _ _)
    (λ { false false c → refl
       ; false true c → sym (⊕-invol true c)
       ; true false c → refl
       ; true true c → refl })

  frame-op-right : (T : B) (y z : fst T)
    → frame T y .fst (op T z) ≡ not (frame T y .fst z)
  frame-op-right T y z = frame-compose T y z (op T z)
    ∙ cong (frame T y .fst z ⊕_) (frame-op T z)
    ∙ ⊕-comm (frame T y .fst z) true

