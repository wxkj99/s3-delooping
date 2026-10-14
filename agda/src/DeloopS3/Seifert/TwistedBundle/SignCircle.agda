{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- A dependent definition on actual torsors,
-- not a recursor on a putative point/loop/square presentation of BC₂.
module DeloopS3.Seifert.TwistedBundle.SignCircle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed using (_→∙_)
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

open import DeloopS3.Seifert.TwistedBundle.OddIntegers public

SignC : B → Type
SignC T = EM (OddAbGroup T) 1

_+S_ : {T : B} → SignC T → SignC T → SignC T
_+S_ {T} = _+ₖ_ {G = OddAbGroup T} {n = 1}

negHom : AbGroupHom ℤAbGroup ℤAbGroup
negHom .fst = -_
negHom .snd = makeIsGroupHom -Dist+

negC : C → C
negC = inducedFun-EM₁ negHom

abstract
  ε : (T : B) (y : fst T) → SignC T ≃ C
  ε T y = isoToEquiv (Iso→EM₁Iso (Odd.evaluation T y))

  ε-base : (T : B) (y : fst T) → ε T y .fst embase ≡ 0C
  ε-base T y = refl

  ε-add : (T : B) (y : fst T) (u v : SignC T)
    → ε T y .fst (_+S_ {T = T} u v) ≡ ε T y .fst u +C ε T y .fst v
  ε-add T y = ClassifyingAddition.B-pres+ {G = OddAbGroup T} {H = ℤAbGroup}
    (GroupIso→GroupHom (Odd.evaluation T y))

  ε-op : (T : B) (y : fst T) (v : SignC T)
    → ε T (op T y) .fst v ≡ negC (ε T y .fst v)
  ε-op T y = EM₁.elimSet (AbGroup→Group (OddAbGroup T))
    (λ _ → emsquash _ _) refl (λ v i j → emloop (v .snd y j) i)

  ε-op-pointed : (T : B) (y : fst T)
    → Path ((SignC T , embase) →∙ (C , 0C))
      (ε T (op T y) .fst , ε-base T (op T y))
      (negC ∘ ε T y .fst , cong negC (ε-base T y))
  ε-op-pointed T y i = (λ v → ε-op T y v i) , refl


rot : {T : B} → SignC T → SignC T ≃ SignC T
rot {T} s = isoToEquiv (addIso {G = OddAbGroup T} 1 s)

sign-circle : (T : B) → PT.∥ SignC T ≃ C ∥₁
sign-circle T = PT.rec PT.squash₁
  (λ e → PT.∣ ε T (invEq e false) ∣₁) (snd T)

sign-groupoid : (T : B) → isGroupoid (SignC T)
sign-groupoid T = emsquash
