{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Products where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; compEquiv ; invEq ; secEq ; retEq)
open import Cubical.Data.Sigma using
  (_×_ ; ΣPathP ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torusSkel ; graph×circleSkel)
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre using (one-equiv)
open import DeloopS3.Bridge.ComponentHomology.Graph using
  (graph-bouquet ; graph-bouquet-unfold)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using
  (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (meridian-chart ; base-chart ; fibre-chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryRealizationProof using
  (original-torus-realization ; concrete-torus-realization
  ; original-core-realization ; concrete-core-realization)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.ProductTop
  public using (module ProductComparison)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Move.CancelMinimal using (T²)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

product-equiv : {A B C D : Type} → A ≃ B → C ≃ D → (A × C) ≃ (B × D)
product-equiv {C = C} e f = compEquiv
  (Σ-cong-equiv-fst {B = λ _ → C} e)
  (Σ-cong-equiv-snd (λ _ → f))

abstract
  product-inverse-pair : {A B C D : Type} (e : A ≃ B) (f : C ≃ D)
    (x : B × D)
    → Path (A × C) (invEq (product-equiv e f) x)
        (invEq e (fst x) , invEq f (snd x))
  product-inverse-pair {A = A} {B = B} {C = C} {D = D} e f x =
    cong (invEq (product-equiv e f)) (sym secpair)
    ∙ retEq (product-equiv e f) z
    where
    z : A × C
    z = invEq e (fst x) , invEq f (snd x)

    secpair : Path (B × D) (fst (product-equiv e f) z) x
    secpair = ΣPathP (secEq e (fst x) , secEq f (snd x))

  original-torus-concrete : Path (T² → realise torusSkel)
    original-torus-realization concrete-torus-realization
  original-torus-concrete = funExt λ (u , t) →
    cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1))))
      (ProductComparison.top-inverse 1
        (invEq one-equiv (invEq S¹≃C u) , invEq S¹≃C t)
      ∙ sym (cong (invEq (Chart.top-chart 1))
          (product-inverse-pair meridian-chart fibre-chart (u , t))))

  original-core-concrete : Path (Literal.Core → realise graph×circleSkel)
    original-core-realization concrete-core-realization
  original-core-concrete = funExt λ (p , t) →
    cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 2))))
      (ProductComparison.top-inverse 2
        (invEq graph-bouquet p , invEq S¹≃C t)
      ∙ cong (λ (e : RoseProduct.Rose 2 ≃ Literal.P) →
          invEq (Chart.top-chart 2)
            (invEq (RoseProduct.suspension-chart 2) (invEq e p) ,
             invEq (RoseProduct.circle-chart 2) (invEq S¹≃C t)))
          graph-bouquet-unfold
      ∙ sym (cong (invEq (Chart.top-chart 2))
          (product-inverse-pair base-chart fibre-chart (p , t))))
