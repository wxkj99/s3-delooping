{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; pushoutEquiv ; symPushout)
open import Cubical.HITs.Wedge using (Iso-⋁genFinSuc-⋁genFin⋁)
open import Cubical.CW.Base using (hasCWskel ; realise)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torusSkel ; graph×circleSkel)
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre using (one-equiv)
open import DeloopS3.Bridge.ComponentHomology.Circle using (C-skeleton)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition using
  (P ; p₀ ; Core ; wedgeLeg ; edge)

-- An exposed copy of Graph.graph-bouquet's construction, including its
-- summand swap (fzero marks d₁).  Its vertex is inr 0C, connected to p₀
-- by sym edge.  We do not silently identify opaque realisation charts.
rose-chart : RoseProduct.Rose 2 ≃ P
rose-chart = compEquiv (isoToEquiv Iso-⋁genFinSuc-⋁genFin⋁)
  (compEquiv
    (pushoutEquiv (λ _ → inl tt) (λ _ → base) wedgeLeg wedgeLeg
      (idEquiv Unit) (compEquiv one-equiv S¹≃C) S¹≃C refl refl)
    (symPushout wedgeLeg wedgeLeg))

meridian-chart : Susp (RoseProduct.Vertices 1) ≃ C
meridian-chart = compEquiv (RoseProduct.suspension-chart 1)
  (compEquiv one-equiv S¹≃C)

base-chart : Susp (RoseProduct.Vertices 2) ≃ P
base-chart = compEquiv (RoseProduct.suspension-chart 2) rose-chart

fibre-chart : Cubical.HITs.Susp.Susp Cubical.Data.Bool.Bool ≃ C
fibre-chart = compEquiv (RoseProduct.circle-chart 1) S¹≃C

private
  torus-product : Chart.Product 1 ≃ T²
  torus-product = compEquiv
    (Σ-cong-equiv-fst {B = λ _ → _} meridian-chart)
    (Σ-cong-equiv-snd (λ _ → fibre-chart))

  core-product : Chart.Product 2 ≃ Core
  core-product = compEquiv
    (Σ-cong-equiv-fst {B = λ _ → _} base-chart)
    (Σ-cong-equiv-snd (λ _ → fibre-chart))

torus-chart : cofib (RoseProduct.attaching 1) ≃ T²
torus-chart = compEquiv (Chart.top-chart 1) torus-product

core-chart : cofib (RoseProduct.attaching 2) ≃ Core
core-chart = compEquiv (Chart.top-chart 2) core-product

abstract
  meridian-point : fst meridian-chart north ≡ 0C
  meridian-point = refl

  base-point : fst base-chart north ≡ p₀
  base-point = sym edge

  fibre-point : fst fibre-chart north ≡ 0C
  fibre-point = refl

  torus-point : fst torus-chart (inr (inl tt)) ≡ (0C , 0C)
  torus-point = cong (fst torus-product) (Chart.on-vertex 1)

concrete-torus-skeleton : hasCWskel T²
concrete-torus-skeleton = torusSkel , compEquiv (invEquiv torus-chart)
  (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1)))

concrete-core-skeleton : hasCWskel Core
concrete-core-skeleton = graph×circleSkel , compEquiv (invEquiv core-chart)
  (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 2)))

concrete-circle-skeleton : hasCWskel C
concrete-circle-skeleton = C-skeleton
