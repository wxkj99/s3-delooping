{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.Coefficients where

-- Product quotient coefficients and a cellular model of the torus multiplier.
-- A quotient comparison identifies the square coefficients with word degrees.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq ; secEq ; retEq)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Pushout using (cofib)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; bouquetSusp→)
open import Cubical.HITs.SphereBouquet.Degree using
  (bouquetDegree ; bouquetDegreeSusp)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torusSkel)
open import DeloopS3.Bridge.CellularPushout.Cellular using
  (restrictCell ; cellular-coefficients)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductMaps using
  (module ProductMap)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using
  (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (meridian-chart ; meridian-point ; fibre-chart ; torus-chart
  ; concrete-torus-skeleton)
open import DeloopS3.Move.CancelMinimal using (T² ; mulC)

module ProductCoefficient (n m : ℕ)
  (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
  (h₀ : h north ≡ north) where
  module PM = ProductMap n m h h₀

  word : SphereBouquet 1 (Fin n) → SphereBouquet 1 (Fin m)
  word = fst (RoseProduct.suspension-chart m) ∘ h
    ∘ invEq (RoseProduct.suspension-chart n)

  square-quotient : SphereBouquet 2 (Fin n) → SphereBouquet 2 (Fin m)
  square-quotient = prefunctoriality.bouquetFunct 3
    (restrictCell PM.cellular 3) (2 , <ᵗsuc {m = 2})

  -- Equality between the cellular square quotient and the suspended word map.
  ProductQuotientGoal : Type
  ProductQuotientGoal = square-quotient ≡ bouquetSusp→ word

  abstract
    square-coefficients-from-quotient : ProductQuotientGoal
      → cellular-coefficients PM.cellular 2 ≡ bouquetDegree word
    square-coefficients-from-quotient q =
      cong bouquetDegree q ∙ sym (bouquetDegreeSusp word)

-- A cellular model of the actual torus multiplier, with realization agreement.
-- Its marked H₂ action is computed in TorusIntegerH2.
module TorusMultiplier (ℓ : ℤ) where
  actual : T² → T²
  actual (u , t) = mulC ℓ u , t

  private
    h : Susp (RoseProduct.Vertices 1) → Susp (RoseProduct.Vertices 1)
    h = invEq meridian-chart ∘ mulC ℓ ∘ fst meridian-chart

    abstract
      h-point : h north ≡ north
      h-point = cong (invEq meridian-chart)
        (cong (mulC ℓ) meridian-point ∙ sym meridian-point)
        ∙ retEq meridian-chart north

    module PM = ProductMap 1 1 h h-point

  cellular : cellMap torusSkel torusSkel
  cellular = PM.cellular

  abstract
    top-agreement : (x : cofib (RoseProduct.attaching 1))
      → fst torus-chart (PM.top x) ≡ actual (fst torus-chart x)
    top-agreement x = cong
      (λ z → fst meridian-chart (fst z) , fst fibre-chart (snd z))
      (PM.top-square x)
      ∙ ΣPathP (secEq meridian-chart
          (mulC ℓ (fst meridian-chart (fst (fst (Chart.top-chart 1) x)))) , refl)

    realise-agreement :
      realiseCellMap cellular ∘ fst (snd concrete-torus-skeleton)
      ≡ fst (snd concrete-torus-skeleton) ∘ actual
    realise-agreement = funExt λ a →
      PM.realise-top (invEq torus-chart a)
      ∙ cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1))))
        (sym (retEq torus-chart (PM.top (invEq torus-chart a)))
          ∙ cong (invEq torus-chart)
            (top-agreement (invEq torus-chart a)
              ∙ cong actual (secEq torus-chart a)))

