{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- A dependent definition on actual torsors,
-- not a recursor on a putative point/loop/square presentation of BC₂.
module DeloopS3.Seifert.TwistedBundle.OddIntegers where

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

open import DeloopS3.Seifert.TwistedBundle.Torsor public

module Odd (T : B) where
  Oddness : (fst T → ℤ) → Type
  Oddness v = (y : fst T) → v (op T y) ≡ - v y

  oddness-prop : (v : fst T → ℤ) → isProp (Oddness v)
  oddness-prop v = isPropΠ λ _ → isSetℤ _ _

  Carrier : Type
  Carrier = Σ (fst T → ℤ) Oddness

  carrier-set : isSet Carrier
  carrier-set = isSetΣ (isSetΠ λ _ → isSetℤ)
    (λ v → isProp→isSet (oddness-prop v))

  zero : Carrier
  zero = (λ _ → pos 0) , (λ _ → refl)

  add : Carrier → Carrier → Carrier
  add (v , hv) (w , hw) = (λ y → v y + w y) ,
    (λ y → cong₂ _+_ (hv y) (hw y) ∙ sym (-Dist+ (v y) (w y)))

  neg : Carrier → Carrier
  neg (v , hv) = (λ y → - v y) , (λ y → cong -_ (hv y))

  eq : {v w : Carrier} → ((y : fst T) → v .fst y ≡ w .fst y) → v ≡ w
  eq h = Σ≡Prop oddness-prop (funExt h)

  group : AbGroup ℓ-zero
  group = makeAbGroup zero add neg carrier-set
    (λ v w u → eq λ y → +Assoc (v .fst y) (w .fst y) (u .fst y))
    (λ v → eq λ y → refl)
    (λ v → eq λ y → -Cancel (v .fst y))
    (λ v w → eq λ y → +Comm (v .fst y) (w .fst y))

  signed : Bool → ℤ → ℤ
  signed false n = n
  signed true n = - n

  signed-not : (b : Bool) (n : ℤ) → signed (not b) n ≡ - signed b n
  signed-not false n = refl
  signed-not true n = sym (-Involutive n)

  extend : fst T → ℤ → Carrier
  extend y n = (λ z → signed (frame T y .fst z) n) ,
    (λ z → cong (λ b → signed b n) (frame-op-right T y z)
      ∙ signed-not (frame T y .fst z) n)

  extend-eval : (y : fst T) (v : Carrier) → extend y (v .fst y) ≡ v
  extend-eval y v = eq λ z →
    bool-case (frame T y .fst z)
    ∙ cong (v .fst) (retEq (frame T y) z)
    where
    bool-case : (b : Bool) → signed b (v .fst y) ≡ v .fst (invEq (frame T y) b)
    bool-case false = cong (v .fst)
      (sym (cong (invEq (frame T y)) (sym (frame-self T y)) ∙ retEq (frame T y) y))
    bool-case true = sym (v .snd y)

  eval-extend : (y : fst T) (n : ℤ) → extend y n .fst y ≡ n
  eval-extend y n = cong (λ b → signed b n) (frame-self T y)

  evaluation : (y : fst T) → AbGroupIso group ℤAbGroup
  evaluation y .fst = iso (λ v → v .fst y) (extend y)
    (eval-extend y) (extend-eval y)
  evaluation y .snd = makeIsGroupHom λ _ _ → refl

OddAbGroup : B → AbGroup ℓ-zero
OddAbGroup = Odd.group

