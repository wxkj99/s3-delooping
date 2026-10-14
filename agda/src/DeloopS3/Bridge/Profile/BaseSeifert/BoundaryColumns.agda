{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup using (AbGroupStr)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.DMCExactness.Geometric using (actual-source)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology
  using (graph-square-pair ; torus-square-coordinate)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ² ; D)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates
open import DeloopS3.Bridge.Profile.BaseSeifert.Reduction using (DegreeTwoComparison)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

open IsGroupHom

-- Actual homology functor equations in the product charts.
-- CofibreHomology.cellular-map-agrees exposes the equality with H̃ᶜʷ→.
record ColumnData (T G : Group₀) (torus-coordinate : fst T → ℤ)
  (core-coordinate : fst G → ℤ × ℤ) (b₁ b₂ b₃ : GroupHom T G) : Type where
  field
    boundary₁-column : (z : fst T)
      → core-coordinate (fst b₁ z) ≡ (torus-coordinate z , pos 0)
    boundary₂-column : (z : fst T)
      → core-coordinate (fst b₂ z) ≡ (pos 0 , torus-coordinate z)
    boundary₃-column : (z : fst T)
      → core-coordinate (fst b₃ z) ≡ (Z.- torus-coordinate z , Z.- torus-coordinate z)

-- Instantiate the abstract group record only AFTER its elaboration.
BoundaryColumns : Type
BoundaryColumns = ColumnData (H̃ᶜʷ torusCW 2) (H̃ᶜʷ graph×circleCW 2)
  torus-square-coordinate graph-square-pair
  (cellular-map torusCW graph×circleCW 2 Literal.boundary₁)
  (cellular-map torusCW graph×circleCW 2 Literal.boundary₂)
  (cellular-map torusCW graph×circleCW 2 Literal.boundary₃)

module BoundaryColumns = ColumnData

private
  _+G_ : fst (H̃ᶜʷ graph×circleCW 2) → fst (H̃ᶜʷ graph×circleCW 2) → fst (H̃ᶜʷ graph×circleCW 2)
  _+G_ = GroupStr._·_ (snd (H̃ᶜʷ graph×circleCW 2))
  _+₂_ : fst ℤ² → fst ℤ² → fst ℤ²
  _+₂_ = AbGroupStr._+_ (snd ℤ²)

  h₁ h₂ h₃ : fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ graph×circleCW 2)
  h₁ = fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₁)
  h₂ = fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₂)
  h₃ = fst (cellular-map torusCW graph×circleCW 2 Literal.boundary₃)

  abstract
    coordinate-plus : (x y : fst (H̃ᶜʷ graph×circleCW 2))
      → graph-square-pair (x +G y) ≡ (graph-square-pair x +₂ graph-square-pair y)
    coordinate-plus x y = sym (core-square-hom-eval (x +G y))
      ∙ pres· (snd core-square-hom) x y
      ∙ cong₂ _+₂_ (core-square-hom-eval x) (core-square-hom-eval y)

    columns-add : (x y z : ℤ)
      → (((x , pos 0) +₂ (pos 0 , y)) +₂ (Z.- z , Z.- z)) ≡ fst D (x , y , z)
    columns-add x y z = ΣPathP
      (cong (Z._+ (Z.- z)) (GroupStr.·IdR (snd ℤGroup) x) ,
       cong (Z._+ (Z.- z)) (GroupStr.·IdL (snd ℤGroup) y))

    left-on-merge : (p q r : ℤ) (x y z : fst (H̃ᶜʷ torusCW 2))
      → fst (cellular-map overlapCW graph×circleCW 2 (Literal.Seifert.allLeft p q r))
          (overlap-merge 1 (2 , refl) x y z) ≡ ((h₁ x +G h₂ y) +G h₃ z)
    left-on-merge p q r x y z =
      map-sum-value tori₂ torusCW overlapCW graph×circleCW 2
        ThreeTori.left ThreeTori.right (Literal.Seifert.allLeft p q r)
        Literal.left12 Literal.boundary₃ refl refl
        (equivFun (fst (TwoTori.sum-equiv 1 (2 , refl))) (x , y)) z
        (overlap-merge 1 (2 , refl) x y z)
        (ThreeTori.sum-equiv-eval 1 (2 , refl)
          (equivFun (fst (TwoTori.sum-equiv 1 (2 , refl))) (x , y)) z)
      ∙ cong (_+G h₃ z)
        (map-sum-value torusCW torusCW tori₂ graph×circleCW 2
          TwoTori.left TwoTori.right Literal.left12 Literal.boundary₁ Literal.boundary₂ refl refl
          x y (equivFun (fst (TwoTori.sum-equiv 1 (2 , refl))) (x , y))
          (TwoTori.sum-equiv-eval 1 (2 , refl) x y))

-- Supplying just the three actual component columns discharges the
-- entire degree-two matrix comparison, for EVERY integer Seifert triple.
-- The right leg disappears because vertices-H₂ projects off its proven
-- contractible H₂, not because the slope maps have been omitted.
abstract
  boundary-columns→degree-two : BoundaryColumns → (p q r : ℤ) → DegreeTwoComparison p q r
  boundary-columns→degree-two cols p q r a =
    cong (λ w → equivFun (fst vertices-H₂)
      (actual-source overlapCW graph×circleCW fillingsCW
        (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 2 w))
      (sym (overlap-split-merge 1 (2 , refl) a))
    ∙ on-components x y z
    ∙ cong (λ w → fst D (equivFun (fst overlap-H₂) w)) (overlap-split-merge 1 (2 , refl) a)
    where
    split : (fst (H̃ᶜʷ torusCW 2) × fst (H̃ᶜʷ torusCW 2)) × fst (H̃ᶜʷ torusCW 2)
    split = equivFun (fst (overlap-splitting 1 (2 , refl))) a
    x y z : fst (H̃ᶜʷ torusCW 2)
    x = fst (fst split)
    y = snd (fst split)
    z = snd split

    c₁ : (x : fst (H̃ᶜʷ torusCW 2)) → graph-square-pair (h₁ x) ≡ (torus-square-coordinate x , pos 0)
    c₁ x = BoundaryColumns.boundary₁-column cols x
    c₂ : (y : fst (H̃ᶜʷ torusCW 2)) → graph-square-pair (h₂ y) ≡ (pos 0 , torus-square-coordinate y)
    c₂ y = BoundaryColumns.boundary₂-column cols y
    c₃ : (z : fst (H̃ᶜʷ torusCW 2)) → graph-square-pair (h₃ z)
      ≡ (Z.- torus-square-coordinate z , Z.- torus-square-coordinate z)
    c₃ z = BoundaryColumns.boundary₃-column cols z

    on-components : (x y z : fst (H̃ᶜʷ torusCW 2))
      → equivFun (fst vertices-H₂)
          (actual-source overlapCW graph×circleCW fillingsCW
            (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 2
            (overlap-merge 1 (2 , refl) x y z))
        ≡ fst D (equivFun (fst overlap-H₂) (overlap-merge 1 (2 , refl) x y z))
    on-components x y z = vertices-H₂-eval _ _
      ∙ cong graph-square-pair (left-on-merge p q r x y z)
      ∙ coordinate-plus (h₁ x +G h₂ y) (h₃ z)
      ∙ cong (_+₂ graph-square-pair (h₃ z)) (coordinate-plus (h₁ x) (h₂ y))
      ∙ cong₂ _+₂_ (cong₂ _+₂_ (c₁ x) (c₂ y)) (c₃ z)
      ∙ columns-add (torus-square-coordinate x) (torus-square-coordinate y) (torus-square-coordinate z)
      ∙ cong (fst D) (sym (overlap-H₂-on-components x y z))
