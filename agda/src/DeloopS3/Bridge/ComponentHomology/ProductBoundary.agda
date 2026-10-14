{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order.Inductive using (_≟ᵗ_ ; lt ; eq ; gt)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Int using (ℤ ; pos ; sumFinℤId ; sumFinℤ0 ; ·Comm)
import Cubical.Data.Int as Z
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Join using (join)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr ; push)
open import Cubical.HITs.Wedge using (_⋁_ ; ⋁↪ ; Iso-⋁genFinSuc-⋁genFin⋁)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using
  (pickPetal ; bouquetDegree ; bouquetDegreeSusp)
open import Cubical.HITs.Sn.Degree using (degree ; degreeConst)
open import Cubical.Algebra.Group.MorphismProperties using (trivGroupHom ; GroupHom≡)
open import Cubical.CW.ChainComplex using (∂)
open import Cubical.CW.Instances.SphereBouquetMap using (SphereBouquet/ˢᵏᵉˡ)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using (bouquetSusp→Charac)
open import DeloopS3.Bridge.ComponentHomology.ProductCells

module Boundary (n : ℕ) where
  open RoseProduct n

  private
    genIso : Iso (SphereBouquet 1 (Fin (suc n))) ((Rose , inl tt) ⋁ (S¹ , base))
    genIso = Iso-⋁genFinSuc-⋁genFin⋁

    shift : Rose → SphereBouquet 1 (Fin (suc n))
    shift = Iso.inv genIso ∘ inl

    shift-zero : (x : Rose) → pickPetal fzero (shift x) ≡ base
    shift-zero (inl tt) = refl
    shift-zero (inr (a , x)) = refl
    shift-zero (push a i) = refl

    shift-pick : (k : Fin n) (x : Rose)
      → pickPetal (fsuc k) (shift x) ≡ pickPetal k x
    shift-pick k (inl tt) = refl
    shift-pick k (inr (a , x)) with fst k ≟ᵗ fst a
    ... | lt p = refl
    ... | eq p = refl
    ... | gt p = refl
    shift-pick k (push a i) with fst k ≟ᵗ fst a
    ... | lt p = refl
    ... | eq p = refl
    ... | gt p = refl

    target-map : Wedge → SphereBouquet 1 (Fin (suc n))
    target-map (inl x) = shift (fst suspension-chart x)
    target-map (inr y) = inr (fzero , fst circle-chart y)
    target-map (push tt i) = push fzero i

    unit-double : {X : Type} {x y : X} (p : x ≡ y)
      → refl ∙∙ p ∙∙ refl ≡ p
    unit-double p = doubleCompPath-elim refl p refl
      ∙ sym (rUnit (refl ∙ p)) ∙ sym (lUnit p)

    target-agrees : fst target-chart ≡ target-map
    target-agrees = funExt λ
      { (inl x) → refl
      ; (inr y) → refl
      ; (push tt i) → λ j →
        cong (cong (Iso.inv genIso)) (unit-double (push tt)) j i }

    coordinate : Fin (suc n) → Susp Vertices × Susp Bool → S¹
    coordinate (0 , p) (x , y) = fst circle-chart y
    coordinate (suc k , p) (x , y) = pickPetal (k , p) (fst suspension-chart x)

    coordinate-extends-direct : (k : Fin (suc n)) (x : Wedge)
      → coordinate k (⋁↪ x) ≡ pickPetal k (target-map x)
    coordinate-extends-direct (0 , p) (inl x) = sym (shift-zero (fst suspension-chart x))
    coordinate-extends-direct (0 , p) (inr y) = refl
    coordinate-extends-direct (0 , p) (push tt i) = refl
    coordinate-extends-direct (suc k , p) (inl x) = sym (shift-pick (k , p) (fst suspension-chart x))
    coordinate-extends-direct (suc k , p) (inr y) = refl
    coordinate-extends-direct (suc k , p) (push tt i) = refl

    coordinate-extends : (k : Fin (suc n)) (x : Wedge)
      → coordinate k (⋁↪ x) ≡ pickPetal k (fst target-chart x)
    coordinate-extends k x = coordinate-extends-direct k x
      ∙ cong (pickPetal k) (sym (funExt⁻ target-agrees x))

  product-coordinate : Fin (suc n) → Susp Vertices × Susp Bool → S¹
  product-coordinate = coordinate

  abstract
    coordinate-on-wedge : (k : Fin (suc n)) (x : Wedge)
      → product-coordinate k (⋁↪ x) ≡ pickPetal k (fst target-chart x)
    coordinate-on-wedge = coordinate-extends

-- ProductBoundary2 computes the zero square differential and H₁/H₂
-- using these product coordinates.
