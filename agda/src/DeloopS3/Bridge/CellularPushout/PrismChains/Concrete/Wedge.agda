{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Wedge where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Wedge using (_⋁_ ; ⋁↪)

record WedgeLift {X Y Z : Type} (x₀ : X) (y₀ : Y) (z₀ : Z)
  (h : X → Y) : Type where
  field
    map : (X , x₀) ⋁ (Z , z₀) → (Y , y₀) ⋁ (Z , z₀)
    point : map (inl x₀) ≡ inl y₀
    square : (w : (X , x₀) ⋁ (Z , z₀))
      → ⋁↪ (map w) ≡ (h (fst (⋁↪ w)) , snd (⋁↪ w))

private
  refl-lift : {X Y Z : Type} (x₀ : X) (z₀ : Z) (h : X → Y)
    → WedgeLift x₀ (h x₀) z₀ h
  WedgeLift.map (refl-lift x₀ z₀ h) (inl x) = inl (h x)
  WedgeLift.map (refl-lift x₀ z₀ h) (inr z) = inr z
  WedgeLift.map (refl-lift x₀ z₀ h) (push a i) = push a i
  WedgeLift.point (refl-lift x₀ z₀ h) = refl
  WedgeLift.square (refl-lift x₀ z₀ h) (inl x) = refl
  WedgeLift.square (refl-lift x₀ z₀ h) (inr z) = refl
  WedgeLift.square (refl-lift x₀ z₀ h) (push a i) = refl

abstract
  wedge-lift : {X Y Z : Type} (x₀ : X) (y₀ : Y) (z₀ : Z)
    (h : X → Y) → h x₀ ≡ y₀ → WedgeLift x₀ y₀ z₀ h
  wedge-lift x₀ y₀ z₀ h = J (λ y p → WedgeLift x₀ y z₀ h)
    (refl-lift x₀ z₀ h)
