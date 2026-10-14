{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CharacterPairs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Bool using (Bool; false; true; not; _and_; _or_; _⊕_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom; compGroupHom; invGroupIso; GroupIso→GroupHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_; ℤ→Fin)
import DeloopS3.Cert.Perm as P
import DeloopS3.Groups.Dihedral as D
open import DeloopS3.Groups.Concrete using (D₈; D₆)

C₂ : Group₀
C₂ = ℤGroup/ 2
zero₂ one₂ : fst C₂
zero₂ = GroupStr.1g (snd C₂)
one₂ = ℤ→Fin 1 (pos 1)

bit₂ : Bool → fst C₂
bit₂ false = zero₂
bit₂ true = one₂

abstract
  bit₂-xor : (b c : Bool) → bit₂ (b ⊕ c) ≡ GroupStr._·_ (snd C₂) (bit₂ b) (bit₂ c)
  bit₂-xor false false = refl
  bit₂-xor false true = refl
  bit₂-xor true false = refl
  bit₂-xor true true = refl

module FiniteCharacter (n e : ℕ) (r s : P.Table)
  (checked : D.PairTables.Checked n e r s)
  (H : Group₀) (comparison : GroupIso (D.PairTables.Build.group n e r s checked) H)
  where
  module T = D.PairTables n e r s
  module B = T.Build checked
  private
    module H = GroupStr (snd H)

  square-test : Bool
  square-test = T.allPairs (λ x → not (snd x) or T.eq (T.mul x x) T.unit)
  rotation-test : Bool
  rotation-test = T.allPairs (λ x → T.allPairs (λ y →
    not (D.sameBool (snd x) false and D.sameBool (snd y) false)
      or T.eq (T.mul x y) (T.mul y x)))

  pairCharacter : GroupHom B.group C₂
  pairCharacter = (λ x → bit₂ (snd x)) , makeIsGroupHom (λ x y → bit₂-xor (snd x) (snd y))

  back : GroupHom H B.group
  back = GroupIso→GroupHom (invGroupIso comparison)

  character : GroupHom H C₂
  character = compGroupHom back pairCharacter

  bit : fst H → Bool
  bit x = snd (fst back x)

  abstract
    back-injective : {x y : fst H} → fst back x ≡ fst back y → x ≡ y
    back-injective {x} {y} p = sym (Iso.sec (fst comparison) x)
      ∙ cong (Iso.fun (fst comparison)) p ∙ Iso.sec (fst comparison) y

    reflection-square : square-test ≡ true → (x : fst H) → bit x ≡ true → x H.· x ≡ H.1g
    reflection-square ok x px = back-injective
      (IsGroupHom.pres· (snd back) x x
       ∙ T.eq-sound _ _ (D.implication
         (T.allPairs-sound (λ x → not (snd x) or T.eq (T.mul x x) T.unit) ok (fst back x)) px)
       ∙ sym (IsGroupHom.pres1 (snd back)))

    rotations-commute : rotation-test ≡ true → (x y : fst H)
      → bit x ≡ false → bit y ≡ false → x H.· y ≡ y H.· x
    rotations-commute ok x y px py = back-injective
      (IsGroupHom.pres· (snd back) x y
       ∙ T.eq-sound _ _ (D.implication
         (T.allPairs-sound (λ y → not (D.sameBool (snd (fst back x)) false and D.sameBool (snd y) false)
           or T.eq (T.mul (fst back x) y) (T.mul y (fst back x)))
           (T.allPairs-sound (λ x → T.allPairs (λ y →
             not (D.sameBool (snd x) false and D.sameBool (snd y) false)
               or T.eq (T.mul x y) (T.mul y x))) ok (fst back x)) (fst back y))
         (cong₂ _and_ (cong (λ b → D.sameBool b false) px) (cong (λ b → D.sameBool b false) py)))
       ∙ sym (IsGroupHom.pres· (snd back) y x))

    character-pair : (x : T.Pair) → fst character (Iso.fun (fst comparison) x) ≡ bit₂ (snd x)
    character-pair x = cong (λ y → bit₂ (snd y)) (Iso.ret (fst comparison) x)

module Eight = FiniteCharacter 4 3 D.r₄ D.s₄ D.checked₈ D₈ D.D₈-pairs≅D₈
module Six = FiniteCharacter 5 2 D.r₃ D.s₃ D.checked₆ D₆ D.D₆-pairs≅D₆

abstract
  square-check₈ : Eight.square-test ≡ true
  square-check₈ = refl
  rotations-check₈ : Eight.rotation-test ≡ true
  rotations-check₈ = refl
  square-check₆ : Six.square-test ≡ true
  square-check₆ = refl
  rotations-check₆ : Six.rotation-test ≡ true
  rotations-check₆ = refl

ε₈ : GroupHom D₈ C₂
ε₈ = Eight.character
ε₆ : GroupHom D₆ C₂
ε₆ = Six.character
