{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryRealizationProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq ; secEq ; retEq)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.Pushout using (cofib)
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (realiseCellMap)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torusSkel ; graph×circleSkel
  ; torus-skeleton ; graph×circle-skeleton)
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using
  (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (rose-chart ; base-chart ; fibre-chart ; torus-chart ; core-chart
  ; concrete-torus-skeleton ; concrete-core-skeleton)
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Products as Products
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

-- Explicit word-chart correction, not an identification with the identity.
word-marking : Literal.Core → Literal.Core
word-marking (p , t) = fst rose-chart (Words.word-chart p) , t

original-torus-realization : T² → realise torusSkel
original-torus-realization = fst (snd torus-skeleton)

original-core-realization : Literal.Core → realise graph×circleSkel
original-core-realization = fst (snd graph×circle-skeleton)

concrete-torus-realization : T² → realise torusSkel
concrete-torus-realization = fst (snd concrete-torus-skeleton)

concrete-core-realization : Literal.Core → realise graph×circleSkel
concrete-core-realization = fst (snd concrete-core-skeleton)

-- Boundary-independent marked-chart comparison: align the product witnesses
-- and absorb the product/graph markings with the explicit word-chart correction.
OriginalMarkedRealizationComparison : Type
OriginalMarkedRealizationComparison =
  Path (T² → realise torusSkel)
    original-torus-realization concrete-torus-realization
  × Path (Literal.Core → realise graph×circleSkel)
    original-core-realization (concrete-core-realization ∘ word-marking)

abstract
  change-markings : {A B X Y : Type} (F : X → Y) (g : A → B)
    (x x' : A → X) (y y' : B → Y)
    → x ≡ x' → y ≡ y' → F ∘ x' ≡ y' ∘ g → F ∘ x ≡ y ∘ g
  change-markings {A = A} {B = B} {X = X} {Y = Y}
    F g x x' y y' px py agreement =
    cong (λ (k : A → X) → F ∘ k) px
    ∙ agreement
    ∙ cong (λ (k : B → Y) → k ∘ g) (sym py)

module WordRealization (d : C → Literal.P) (d₀ : d 0C ≡ Literal.p₀) where
  module W = Products.WordProduct d d₀

  abstract
    top-agreement : (x : cofib (RoseProduct.attaching 1))
      → fst core-chart (W.PM.top x)
        ≡ word-marking (W.actual (fst torus-chart x))
    top-agreement x =
      cong (λ (z : Chart.Product 2) →
        fst base-chart (fst z) , fst fibre-chart (snd z))
        (W.PM.top-square x)
      ∙ ΣPathP (cong (fst rose-chart)
          (secEq (RoseProduct.suspension-chart 2)
            (Words.word-bouquet d
              (fst (RoseProduct.suspension-chart 1)
                (fst (fst (Chart.top-chart 1) x))))) , refl)

    -- Use WordProduct's cellular map rather than WordCircle's
    -- differently conjugated pointed map.
    concrete-word-realise : Path (T² → realise graph×circleSkel)
      (realiseCellMap W.PM.cellular ∘ concrete-torus-realization)
      (concrete-core-realization ∘ word-marking ∘ W.actual)
    concrete-word-realise = funExt λ a →
      W.PM.realise-top (invEq torus-chart a)
      ∙ cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 2))))
        (sym (retEq core-chart (W.PM.top (invEq torus-chart a)))
          ∙ cong (invEq core-chart)
            (top-agreement (invEq torus-chart a)
              ∙ cong (word-marking ∘ W.actual) (secEq torus-chart a)))

    marked-realise : OriginalMarkedRealizationComparison → W.RealizationAgreement
    marked-realise c = change-markings (realiseCellMap W.PM.cellular) W.actual
      original-torus-realization concrete-torus-realization
      original-core-realization (concrete-core-realization ∘ word-marking)
      (fst c) (snd c) concrete-word-realise

abstract
  boundary-realization-agreements-from-comparison :
    OriginalMarkedRealizationComparison → Products.BoundaryRealizationAgreements
  boundary-realization-agreements-from-comparison c =
    WordRealization.marked-realise Literal.d₁ refl c ,
    (WordRealization.marked-realise Literal.d₂ (sym Literal.edge) c ,
     WordRealization.marked-realise Literal.d₃ refl c)
