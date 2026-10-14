{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.ProductTop where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_ ; invEq)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Pushout using
  (Pushout ; cofib ; inl ; inr ; push ; symPushout)
open import DeloopS3.Compat.Whitehead using
  (Iso-Susp×Susp-cofibJoinTo⋁)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using
  (module Chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Rechart using
  (module Rechart ; cofibre-rechart-inverse)

abstract
  swap-inverse : {A B C : Type} (f : A → B) (g : A → C)
    (x : Pushout f g)
    → Path (Pushout g f) (fst (symPushout f g) x)
        (invEq (symPushout g f) x)
  swap-inverse f g (inl b) = refl
  swap-inverse f g (inr c) = refl
  swap-inverse f g (push a i) = refl

module ProductComparison (n : ℕ) where
  open RoseProduct n

  private
    lower : Rose × S¹ → Chart.Product n
    lower z = invEq suspension-chart (fst z) , invEq circle-chart (snd z)

    front : Rose × S¹ → cofib W
    front = fst (symPushout W (λ _ → tt))
      ∘ Iso.fun (Iso-Susp×Susp-cofibJoinTo⋁ Vertices Bool (inl tt) true)
      ∘ lower

  abstract
    top-inverse : (z : Rose × S¹)
      → Path (cofib attaching)
          (fst product-cofibre z)
          (invEq (Chart.top-chart n)
            (invEq suspension-chart (fst z) , invEq circle-chart (snd z)))
    top-inverse z =
      cong (λ (e : (Rose × S¹) ≃ cofib attaching) → fst e z)
        product-cofibre-unfold
      ∙ cong (λ (e : cofib W ≃ cofib attaching) → fst e (front z))
        (cofibre-rechart-inverse source-chart target-chart W)
      ∙ cong (invEq (Rechart.backward source-chart target-chart W))
        (swap-inverse W (λ _ → tt)
          (Iso.fun (Iso-Susp×Susp-cofibJoinTo⋁ Vertices Bool (inl tt) true)
            (lower z)))
