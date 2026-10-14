{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; pushoutEquiv ; symPushout)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.Wedge using (⋁↪)
open import DeloopS3.Compat.Whitehead using
  (Iso-Susp×Susp-cofibJoinTo⋁ ; Susp×Susp→cofibW≡)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)

-- Same skeleton and attaching map as ComponentHomology.ProductCells.
-- A reverse chart with an exposed restriction, rather than unfolding the
-- opaque product-cofibre equivalence at every use.
module Chart (n : ℕ) where
  open RoseProduct n

  Product : Type
  Product = Susp Vertices × Susp Bool

  private
    rechart : cofib attaching ≃ cofib W
    rechart = pushoutEquiv (λ _ → tt) attaching (λ _ → tt) W
      source-chart (idEquiv Unit) (invEquiv target-chart) refl
      (funExt λ x → retEq target-chart (W (fst source-chart x)))

    whitehead : cofib W ≃ Product
    whitehead = compEquiv (symPushout (λ _ → tt) W)
      (invEquiv (isoToEquiv
        (Iso-Susp×Susp-cofibJoinTo⋁ Vertices Bool (inl tt) true)))

  top-chart : cofib attaching ≃ Product
  top-chart = compEquiv rechart whitehead

  abstract
    target-point : fst target-chart (inl north) ≡ inl tt
    target-point = refl

    target-inverse-point : invEq target-chart (inl tt) ≡ inl north
    target-inverse-point = cong (invEq target-chart) (sym target-point)
      ∙ retEq target-chart (inl north)

    on-edge : (x : SphereBouquet 1 (Fin (suc n)))
      → fst top-chart (inr x) ≡ ⋁↪ (invEq target-chart x)
    on-edge x = funExt⁻
      (Susp×Susp→cofibW≡ Vertices Bool (inl tt) true)
      (invEq target-chart x)

    on-vertex : fst top-chart (inr (inl tt)) ≡ (north , north)
    on-vertex = on-edge (inl tt) ∙ cong ⋁↪ target-inverse-point
