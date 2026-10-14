{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusIntegerCircle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; ℤHom)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.Circle using
  (circleCW ; C-finite ; circle-H₁ ; circle-coordinate)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coproduct using (module Coproduct)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (map-square)
open import DeloopS3.Bridge.Profile.BaseSeifert.HurewiczChartProof using (circle-integer-coordinate)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components using (circle-integer)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass using (loop-natural)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; mulC)
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerAlgebra
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerCylinder using (overlapCW)

circle-map : ℤ → GroupHom (H̃ᶜʷ circleCW 1) (H̃ᶜʷ circleCW 1)
circle-map ℓ = cellular-map circleCW circleCW 1 (mulC ℓ)

abstract
  circle-integer-section : (x : fst (H̃ᶜʷ circleCW 1))
    → fst circle-integer (circle-coordinate x) ≡ x
  circle-integer-section x = equiv-injective circle-H₁ _ _
    (circle-integer-coordinate (circle-coordinate x))

  circle-integer-natural : (ℓ n : ℤ)
    → fst (circle-map ℓ) (fst circle-integer n) ≡ fst circle-integer (ℓ Z.· n)
  circle-integer-natural ℓ n =
    loop-natural circleCW circleCW (mulC ℓ) 0C (emloop {Group = ℤGroup} n)

  circle-multiplier-coordinate : (ℓ : ℤ) (x : fst (H̃ᶜʷ circleCW 1))
    → circle-coordinate (fst (circle-map ℓ) x) ≡ ℓ Z.· circle-coordinate x
  circle-multiplier-coordinate ℓ x =
    cong (circle-coordinate ∘ fst (circle-map ℓ)) (sym (circle-integer-section x))
    ∙ cong circle-coordinate (circle-integer-natural ℓ (circle-coordinate x))
    ∙ circle-integer-coordinate (ℓ Z.· circle-coordinate x)

  circle-multiplier-scalar : (ℓ : ℤ) → Scalar (H̃ᶜʷ circleCW 1) ℓ (circle-map ℓ)
  circle-multiplier-scalar ℓ = scalar-through-equiv circle-H₁
    (circle-map ℓ) (ℤHom ℓ) ℓ (circle-multiplier-coordinate ℓ) (integer-scalar ℓ)

module SumCircle = Coproduct circleCW circleCW overlapCW
  (idEquiv (C Sum.⊎ C)) 1 1 C-finite C-finite

private
  module SumAlgebra = CoproductScalar (H̃ᶜʷ circleCW 1) (H̃ᶜʷ overlapCW 1)
    (cellular-map circleCW overlapCW 1 Sum.inl)
    (cellular-map circleCW overlapCW 1 Sum.inr)
    (SumCircle.sum-equiv 0 (3 , refl))
    (SumCircle.sum-equiv-eval 0 (3 , refl))

  overlap-map : ℤ → GroupHom (H̃ᶜʷ overlapCW 1) (H̃ᶜʷ overlapCW 1)
  overlap-map ℓ = cellular-map overlapCW overlapCW 1 (Sum.map (mulC ℓ) (mulC ℓ))

  abstract
    left-square : (ℓ : ℤ) (x : fst (H̃ᶜʷ circleCW 1))
      → fst (overlap-map ℓ) (fst (cellular-map circleCW overlapCW 1 Sum.inl) x)
        ≡ fst (cellular-map circleCW overlapCW 1 Sum.inl) (fst (circle-map ℓ) x)
    left-square ℓ x =
      map-square circleCW overlapCW overlapCW 1 Sum.inl (Sum.map (mulC ℓ) (mulC ℓ))
        (Sum.inl ∘ mulC ℓ) refl x
      ∙ sym (map-square circleCW circleCW overlapCW 1 (mulC ℓ) Sum.inl
        (Sum.inl ∘ mulC ℓ) refl x)

    right-square : (ℓ : ℤ) (x : fst (H̃ᶜʷ circleCW 1))
      → fst (overlap-map ℓ) (fst (cellular-map circleCW overlapCW 1 Sum.inr) x)
        ≡ fst (cellular-map circleCW overlapCW 1 Sum.inr) (fst (circle-map ℓ) x)
    right-square ℓ x =
      map-square circleCW overlapCW overlapCW 1 Sum.inr (Sum.map (mulC ℓ) (mulC ℓ))
        (Sum.inr ∘ mulC ℓ) refl x
      ∙ sym (map-square circleCW circleCW overlapCW 1 (mulC ℓ) Sum.inr
        (Sum.inr ∘ mulC ℓ) refl x)

abstract
  overlap-multiplier-scalar : (ℓ : ℤ) → Scalar (H̃ᶜʷ overlapCW 1) ℓ
    (H̃ᶜʷ→ {C = overlapCW} {D = overlapCW} 1 (Sum.map (mulC ℓ) (mulC ℓ)))
  overlap-multiplier-scalar ℓ = subst (Scalar (H̃ᶜʷ overlapCW 1) ℓ)
    (cellular-map-agrees overlapCW overlapCW 1 (Sum.map (mulC ℓ) (mulC ℓ)))
    (SumAlgebra.scalar-on-sum (circle-map ℓ) (overlap-map ℓ) ℓ
      (left-square ℓ) (right-square ℓ) (circle-multiplier-scalar ℓ))
