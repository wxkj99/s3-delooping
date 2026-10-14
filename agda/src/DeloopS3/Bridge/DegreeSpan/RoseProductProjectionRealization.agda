{-# OPTIONS --cubical --safe --lossy-unification #-}
open import Cubical.Data.Nat using (ℕ)

module DeloopS3.Bridge.DegreeSpan.RoseProductProjectionRealization (n : ℕ) where

-- The actual sparse cellular map realizes petal projection for every rose.
-- Only the target is required to be a groupoid.  No source truncation or
-- realization hypothesis is used.
open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Order.Inductive using (_≟ᵗ_ ; lt ; eq ; gt)
open import Cubical.Data.Fin using (Fin ; fzero)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid ; suspFun ; toSusp)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; sphereBouquetSuspIso₀)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.Wedge using (⋁↪ ; ⋁gen)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash)
open import Cubical.CW.Base using (realise)
open import Cubical.CW.Map using (realiseCellMap)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (meridian-chart ; fibre-chart ; torus-chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Products using
  (product-equiv ; product-inverse-pair ; original-torus-concrete ; module ProductComparison)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC)
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Realization using (module CircleAttachment)
open import DeloopS3.Bridge.DegreeSpan.RoseProductProjectionSparse n

project : Fin n → RoseProduct.Rose n × S¹ → T²
project j (u , t) = circleToC (pickPetal j u) , circleToC t

rose-product-chart : cofib (RoseProduct.attaching n) ≃ (RoseProduct.Rose n × S¹)
rose-product-chart = compEquiv (Chart.top-chart n)
  (product-equiv (RoseProduct.suspension-chart n) (RoseProduct.circle-chart n))

abstract
  original-product-concrete :
    fst (snd (RoseProduct.has-skeleton n))
      ≡ fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching n))) ∘ invEq rose-product-chart
  original-product-concrete = funExt λ z →
    cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching n))))
      (ProductComparison.top-inverse n z
        ∙ sym (cong (invEq (Chart.top-chart n))
            (product-inverse-pair (RoseProduct.suspension-chart n)
              (RoseProduct.circle-chart n) z)))

  cell-inclusion : (r : ℕ) (x : SphereBouquet 1 (Fin (suc r)))
    → invEq (cell-attachment r) (inl x) ≡ inr x
  cell-inclusion r x = refl

private
  coordinate : Fin n → Susp (RoseProduct.Vertices n) → C
  coordinate j = circleToC ∘ pickPetal j ∘ fst (RoseProduct.suspension-chart n)

  read-suspended : (r : ℕ) → Fin r
    → ⋁gen (Fin r) (λ _ → Susp Bool , north) → C
  read-suspended r j = circleToC ∘ pickPetal j ∘ Iso.fun sphereBouquetSuspIso₀

  petal-path : {r : ℕ} (k : Fin r) (b : Bool)
    → Path (⋁gen (Fin r) (λ _ → Susp Bool , north))
        (inr (k , north)) (inr (k , north))
  petal-path k b i = inr (k , toSusp (Bool , true) b i)

  SelectionMeridian : (j : Fin n) (a : RoseProduct.Vertices n) → Type
  SelectionMeridian j a = Path (0C ≡ 0C)
    (cong (fst meridian-chart) (merid (vertexSelection j a)))
    (cong (coordinate j) (merid a))

  abstract
    -- Expose the three mapped paths before deciding equality.  This keeps
    -- the decision in the expected type, rather than asking conversion to
    -- propagate a with-clause through an inferred cong-∙∙ application.
    selection-meridian-normal : (j k : Fin n) (b : Bool)
      → Path (0C ≡ 0C)
          (cong (fst meridian-chart) (merid (vertexSelection j (inr (k , b)))))
          (cong (read-suspended n j) (push k)
            ∙∙ cong (read-suspended n j) (petal-path k b)
            ∙∙ cong (read-suspended n j) (sym (push k)))
    selection-meridian-normal j k b with fst j ≟ᵗ fst k
    ... | lt _ = rUnit refl
    ... | eq _ = cong-∙∙ (read-suspended 1 fzero)
        (push fzero) (petal-path fzero b) (sym (push fzero))
    ... | gt _ = rUnit refl

    selection-meridian-petal : (j k : Fin n) (b : Bool)
      → SelectionMeridian j (inr (k , b))
    selection-meridian-petal j k b = selection-meridian-normal j k b
      ∙ sym (cong-∙∙ (read-suspended n j)
          (push k) (petal-path k b) (sym (push k)))

    selection-meridian : (j : Fin n) (a : RoseProduct.Vertices n)
      → SelectionMeridian j a
    selection-meridian j (inl tt) = refl
    selection-meridian j (inr (k , b)) = selection-meridian-petal j k b
    selection-meridian j (push k i) =
      isProp→PathP {B = λ i → SelectionMeridian j (push k i)}
        (λ i → emsquash 0C 0C
          (cong (fst meridian-chart) (merid (vertexSelection j (push k i))))
          (cong (coordinate j) (merid (push k i))))
        refl (selection-meridian-petal j k true) i

    meridian-selection : (j : Fin n) (a : Susp (RoseProduct.Vertices n))
      → fst meridian-chart (suspFun (vertexSelection j) a) ≡ coordinate j a
    meridian-selection j north = refl
    meridian-selection j south = refl
    meridian-selection j (merid a i) r = selection-meridian j a r i

  torus-product : Chart.Product 1 → T²
  torus-product (a , b) = fst meridian-chart a , fst fibre-chart b

  rose-product : Chart.Product n → RoseProduct.Rose n × S¹
  rose-product (a , b) = fst (RoseProduct.suspension-chart n) a , fst (RoseProduct.circle-chart n) b

  suspension-product : Fin n → Chart.Product n → Chart.Product 1
  suspension-product j (a , b) = suspFun (vertexSelection j) a , b

  abstract
    wedge-product : (j : Fin n) (w : RoseProduct.Wedge n)
      → Path (Chart.Product 1) (⋁↪ (wedgeSelection j w))
          (suspension-product j (⋁↪ w))
    wedge-product j (inl a) = refl
    wedge-product j (inr b) = refl
    wedge-product j (push tt i) = refl

    lower-marked : (j : Fin n) (x : SphereBouquet 1 (Fin (suc n)))
      → fst torus-chart (inr (lower j x))
        ≡ project j (fst rose-product-chart (inr x))
    lower-marked j x =
      cong torus-product (Chart.on-edge 1 (lower j x))
      ∙ cong (torus-product ∘ ⋁↪)
          (retEq (RoseProduct.target-chart 1)
            (wedgeSelection j (invEq (RoseProduct.target-chart n) x)))
      ∙ cong torus-product
          (wedge-product j (invEq (RoseProduct.target-chart n) x))
      ∙ ΣPathP
          (meridian-selection j (fst (⋁↪ (invEq (RoseProduct.target-chart n) x))) , refl)
      ∙ sym (cong (project j ∘ rose-product) (Chart.on-edge n x))

module RealizationStage (j : Fin n) where
  private
    F G : Pushout (cell-attaching n) fst → T²
    F = fst torus-chart ∘ sparseTop j ∘ invEq (cell-attachment n)
    G = project j ∘ fst rose-product-chart ∘ invEq (cell-attachment n)

    abstract
      on-lower : (x : SphereBouquet 1 (Fin (suc n))) → F (inl x) ≡ G (inl x)
      on-lower x =
        cong (fst torus-chart) (sym (SparseStage.Stage.comm j x))
        ∙ cong (fst torus-chart) (cell-inclusion 1 (lower j x))
        ∙ lower-marked j x
        ∙ sym (cong (project j ∘ fst rose-product-chart) (cell-inclusion n x))

  abstract
    top-marked : (z : cofib (RoseProduct.attaching n))
      → fst torus-chart (sparseTop j z)
        ≡ project j (fst rose-product-chart z)
    top-marked z =
      sym (cong (fst torus-chart ∘ sparseTop j) (retEq (cell-attachment n) z))
      ∙ CircleAttachment.homotopy (cell-attaching n)
          (isGroupoidΣ emsquash (λ _ → emsquash)) F G on-lower
          (fst (cell-attachment n) z)
      ∙ cong (project j ∘ fst rose-product-chart) (retEq (cell-attachment n) z)

abstract
  sparse-marked-agreement : (j : Fin n)
    → realiseCellMap (sparseCellular j) ∘ fst (snd (RoseProduct.has-skeleton n))
      ≡ fst (snd torus-skeleton) ∘ project j
  sparse-marked-agreement j = funExt λ a →
    cong (realiseCellMap (sparseCellular j)) (funExt⁻ original-product-concrete a)
    ∙ sparseCellular-realise-top j (invEq rose-product-chart a)
    ∙ cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1))))
        (sym (retEq torus-chart (sparseTop j (invEq rose-product-chart a)))
          ∙ cong (invEq torus-chart)
              (RealizationStage.top-marked j (invEq rose-product-chart a)
                ∙ cong (project j) (secEq rose-product-chart a)))
    ∙ sym (funExt⁻ original-torus-concrete (project j a))
