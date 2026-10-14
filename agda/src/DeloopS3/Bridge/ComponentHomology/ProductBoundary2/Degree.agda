{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Degree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Int using (ℤ ; pos ; sumFinℤ ; sumFinℤ0 ; ·AnnihilR)
import Cubical.Data.Int as Z
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Join using (join)
open import Cubical.HITs.Pushout using (inl ; inr)
open import Cubical.HITs.Wedge using (⋁↪)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree)
open import Cubical.HITs.Sn.Degree using (degree ; degreeConst)
open import Cubical.Algebra.Group.MorphismProperties using (trivGroupHom ; GroupHom≡)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary using (module Boundary)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Paths

abstract
  coordinate-null→degree-zero : {m k : ℕ} (f : FinSphereBouquetMap m k 0)
    → ((b : Fin k) (x : SphereBouquet 1 (Fin m)) → pickPetal b (f x) ≡ base)
    → bouquetDegree f ≡ trivGroupHom
  coordinate-null→degree-zero {m} f null = GroupHom≡ (funExt λ r → funExt λ b →
    (λ i → sumFinℤ λ a → r a Z.·
      (cong (degree 1) (funExt λ x → null b (inr (a , x))) ∙ degreeConst 1) i)
    ∙ (λ i → sumFinℤ λ a → ·AnnihilR (r a) i)
    ∙ sumFinℤ0 m)

module ProductNull (n : ℕ) where
  open RoseProduct n
  open Boundary n

  abstract
    product-null : (x : join Vertices Bool)
      → Path (Susp Vertices × Susp Bool) (⋁↪ (W x)) (north , north)
    product-null = JoinNull.join-to-product-null Vertices Bool (inl tt) true

  private
    coordinate-origin : (k : Fin (suc n))
      → product-coordinate k (north , north) ≡ base
    coordinate-origin (0 , p) = refl
    coordinate-origin (suc k , p) = refl

  abstract
    attaching-coordinate-null : (k : Fin (suc n)) (x : Rose)
      → pickPetal k (attaching x) ≡ base
    attaching-coordinate-null k x =
      sym (coordinate-on-wedge k (W (fst source-chart x)))
      ∙ cong (product-coordinate k) (product-null (fst source-chart x))
      ∙ coordinate-origin k

    attaching-degree-zero : bouquetDegree attaching ≡ trivGroupHom
    attaching-degree-zero = coordinate-null→degree-zero attaching attaching-coordinate-null
