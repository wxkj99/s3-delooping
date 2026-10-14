{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.Character where

-- Finite algebra only. Generation is used only by elimination into
-- propositions; no representative of a merely given normal form is chosen.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty as Empty using (⊥)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom; GroupHom≡)
open import DeloopS3.Bridge.SpanPi1.CharacterAlgebra public
open import DeloopS3.Bridge.SpanPi1.CharacterPairs public
open import DeloopS3.Bridge.SpanPi1.CharacterWitnesses public
open import DeloopS3.Bridge.SpanPi1.CharacterImages public
open import DeloopS3.Cert.Interpret.Short using (ShortCase; octa; icosa; H)

record KleinCharacter (K : Group₀) (χ : GroupHom K C₂) : Type₀ where
  private module K = GroupStr (snd K)
  field
    r j : fst K
    inversion : j K.· r ≡ K.inv r K.· j
    generated : KleinNF K r j
    r-zero : fst χ r ≡ zero₂
    j-one : fst χ j ≡ one₂

rotationCharacter : (c : ShortCase) → GroupHom (H c) C₂
rotationCharacter octa = ε₈
rotationCharacter icosa = ε₆

abstract
  rotationCharacter-rotation : (c : ShortCase) → fst (rotationCharacter c) (rotation c) ≡ zero₂
  rotationCharacter-rotation octa = ε₈-rotation
  rotationCharacter-rotation icosa = ε₆-rotation

  rotationCharacter-reflection : (c : ShortCase) → fst (rotationCharacter c) (reflection c) ≡ one₂
  rotationCharacter-reflection octa = ε₈-reflection
  rotationCharacter-reflection icosa = ε₆-reflection

private
  not-true : (b : Bool) → (b ≡ true → ⊥) → b ≡ false
  not-true false p = refl
  not-true true p = Empty.rec (p refl)
  not-false : (b : Bool) → (b ≡ false → ⊥) → b ≡ true
  not-false false p = Empty.rec (p refl)
  not-false true p = refl

module Rigidity (H₀ : Group₀) (ε : GroupHom H₀ C₂) (bit : fst H₀ → Bool)
  (value : (x : fst H₀) → fst ε x ≡ bit₂ (bit x))
  (reflection-square : (x : fst H₀) → bit x ≡ true
    → GroupStr._·_ (snd H₀) x x ≡ GroupStr.1g (snd H₀))
  (rotations-commute : (x y : fst H₀) → bit x ≡ false → bit y ≡ false
    → GroupStr._·_ (snd H₀) x y ≡ GroupStr._·_ (snd H₀) y x) where
  private module H₀ = GroupStr (snd H₀)

  abstract
    rigid : (K : Group₀) (χ : GroupHom K C₂) (λ₀ : GroupHom K H₀)
      → KleinCharacter K χ → NonabelianImage λ₀
      → (u : fst K) → fst χ u ≡ fst ε (fst λ₀ u)
    rigid K χ λ₀ kc nonab = Generation.agree K C₂ r j generated
      χ (compGroupHom λ₀ ε)
      (r-zero ∙ sym (value a ∙ cong bit₂ a-rotation))
      (j-one ∙ sym (value b ∙ cong bit₂ b-reflection))
      where
      open KleinCharacter kc
      a b : fst H₀
      a = fst λ₀ r
      b = fst λ₀ j
      noncomm : a H₀.· b ≡ b H₀.· a → ⊥
      noncomm = Generation.noncommuting-generators K H₀ r j generated λ₀ nonab
      relation : b H₀.· a ≡ H₀.inv a H₀.· b
      relation = sym (IsGroupHom.pres· (snd λ₀) j r)
        ∙ cong (fst λ₀) inversion ∙ IsGroupHom.pres· (snd λ₀) _ j
        ∙ cong (H₀._· b) (IsGroupHom.presinv (snd λ₀) r)
      square-nontrivial : a H₀.· a ≡ H₀.1g → ⊥
      square-nontrivial sq = noncomm (Commutation.square-inversion-commute H₀ a b relation sq)
      a-rotation : bit a ≡ false
      a-rotation = not-true (bit a) (λ p → square-nontrivial (reflection-square a p))
      b-reflection : bit b ≡ true
      b-reflection = not-false (bit b) (λ p → noncomm (rotations-commute a b a-rotation p))

module Rigid₈ = Rigidity _ ε₈ Eight.bit (λ x → refl)
  (Eight.reflection-square square-check₈) (Eight.rotations-commute rotations-check₈)
module Rigid₆ = Rigidity _ ε₆ Six.bit (λ x → refl)
  (Six.reflection-square square-check₆) (Six.rotations-commute rotations-check₆)

abstract
  dihedral-character-rigid : (c : ShortCase) (K : Group₀)
    (χ : GroupHom K C₂) (λ₀ : GroupHom K (H c))
    → KleinCharacter K χ → NonabelianImage λ₀
    → (u : fst K) → fst χ u ≡ fst (rotationCharacter c) (fst λ₀ u)
  dihedral-character-rigid octa = Rigid₈.rigid
  dihedral-character-rigid icosa = Rigid₆.rigid

  dihedral-character-equality : (c : ShortCase) (K : Group₀)
    (χ : GroupHom K C₂) (λ₀ : GroupHom K (H c))
    → KleinCharacter K χ → NonabelianImage λ₀
    → χ ≡ compGroupHom λ₀ (rotationCharacter c)
  dihedral-character-equality c K χ λ₀ kc nonab =
    GroupHom≡ (funExt (dihedral-character-rigid c K χ λ₀ kc nonab))

  dihedral-character-rigid-merely : (c : ShortCase) (K : Group₀)
    (χ : GroupHom K C₂) (λ₀ : GroupHom K (H c))
    → PT.∥ KleinCharacter K χ ∥₁ → NonabelianImage λ₀
    → (u : fst K) → fst χ u ≡ fst (rotationCharacter c) (fst λ₀ u)
  dihedral-character-rigid-merely c K χ λ₀ merely nonab u =
    PT.rec (GroupStr.is-set (snd C₂) _ _)
      (λ kc → dihedral-character-rigid c K χ λ₀ kc nonab u) merely
