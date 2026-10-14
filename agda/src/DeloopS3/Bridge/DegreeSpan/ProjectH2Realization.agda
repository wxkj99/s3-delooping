{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ProjectH2Realization where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.S1.Properties using (isConnectedS¹)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid ; suspFun ; toSusp ; S¹IsoSuspBool)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; sphereBouquetSuspIso₀)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.Wedge using (⋁↪ ; ⋁gen)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash)
open import Cubical.CW.Map using (realiseCellMap)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton ; graph×circle-skeleton)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (rose-chart ; base-chart ; meridian-chart ; fibre-chart ; torus-chart ; core-chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison using
  (word-marking-id ; original-torus-concrete ; original-core-concrete)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC)
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
import DeloopS3.Bridge.DegreeSpan.ProjectH2 as ProjectH2
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse hiding (project-H₂)

-- Agreement on the lower stage extends across circle-attached two-cells
-- when the target is a 1-type.  Centres are not chosen by groupoidness:
-- each is transported along the actual spoke at base.  Only the ensuing
-- square (not the pointwise path) is proposition-valued.
module CircleAttachment {X K T : Type} (α : K × S¹ → X)
  (hT : isGroupoid T) (F G : Pushout α fst → T)
  (H : (x : X) → F (inl x) ≡ G (inl x)) where

  private
    E : Pushout α fst → Type
    E z = F z ≡ G z

    centre : (k : K) → E (inr k)
    centre k = subst E (push (k , base)) (H (α (k , base)))

    Boundary : (k : K) → S¹ → Type
    Boundary k s = PathP (λ i → E (push (k , s) i))
      (H (α (k , s))) (centre k)

    boundary-prop : (k : K) (s : S¹) → isProp (Boundary k s)
    boundary-prop k s = isOfHLevelPathP' 1 (hT _ _) _ _

    anchor : (k : K) → Boundary k base
    anchor k = toPathP refl

    boundary : (k : K) (s : S¹) → Boundary k s
    boundary k s = PT.rec (boundary-prop k s)
      (λ p → subst (Boundary k) p (anchor k)) (isConnectedS¹ s)

  homotopy : (z : Pushout α fst) → F z ≡ G z
  homotopy (inl x) = H x
  homotopy (inr k) = centre k
  homotopy (push (k , s) i) = boundary k s i

abstract
  cell-inclusion : (n : ℕ) (x : SphereBouquet 1 (Fin (suc n)))
    → invEq (cell-attachment n) (inl x) ≡ inr x
  cell-inclusion n x = refl

private
  coordinate : Fin 2 → Susp (RoseProduct.Vertices 2) → C
  coordinate j = circleToC ∘ pickPetal j ∘ fst (RoseProduct.suspension-chart 2)

  read-suspended : (n : ℕ) → Fin n
    → ⋁gen (Fin n) (λ _ → Susp Bool , north) → C
  read-suspended n j = circleToC ∘ pickPetal j ∘ Iso.fun sphereBouquetSuspIso₀

  petal-path : {n : ℕ} (k : Fin n) (b : Bool)
    → Path (⋁gen (Fin n) (λ _ → Susp Bool , north))
        (inr (k , north)) (inr (k , north))
  petal-path k b i = inr (k , toSusp (Bool , true) b i)

  SelectionMeridian : (j : Fin 2) (a : RoseProduct.Vertices 2) → Type
  SelectionMeridian j a = Path (0C ≡ 0C)
    (cong (fst meridian-chart) (merid (vertexSelection j a)))
    (cong (coordinate j) (merid a))

  abstract
    selection-meridian-petal : (j k : Fin 2) (b : Bool)
      → SelectionMeridian j (inr (k , b))
    selection-meridian-petal (zero , _) (zero , _) b =
      cong-∙∙ (read-suspended 1 fzero)
        (push fzero) (petal-path fzero b) (sym (push fzero))
      ∙ sym (cong-∙∙ (read-suspended 2 fzero)
        (push fzero) (petal-path fzero b) (sym (push fzero)))
    selection-meridian-petal (zero , _) (suc zero , _) b =
      sym (cong-∙∙ (read-suspended 2 fzero)
        (push (fsuc fzero)) (petal-path (fsuc fzero) b) (sym (push (fsuc fzero)))
        ∙ sym (rUnit refl))
    selection-meridian-petal (suc zero , _) (zero , _) b =
      sym (cong-∙∙ (read-suspended 2 (fsuc fzero))
        (push fzero) (petal-path fzero b) (sym (push fzero))
        ∙ sym (rUnit refl))
    selection-meridian-petal (suc zero , _) (suc zero , _) b =
      cong-∙∙ (read-suspended 1 fzero)
        (push fzero) (petal-path fzero b) (sym (push fzero))
      ∙ sym (cong-∙∙ (read-suspended 2 (fsuc fzero))
        (push (fsuc fzero)) (petal-path (fsuc fzero) b) (sym (push (fsuc fzero))))
    selection-meridian-petal (suc (suc n) , ()) _ _
    selection-meridian-petal _ (suc (suc n) , ()) _

    selection-meridian : (j : Fin 2) (a : RoseProduct.Vertices 2)
      → SelectionMeridian j a
    selection-meridian j (inl tt) = refl
    selection-meridian j (inr (k , b)) = selection-meridian-petal j k b
    selection-meridian j (push k i) =
      isProp→PathP {B = λ i → SelectionMeridian j (push k i)}
        (λ i → emsquash 0C 0C
          (cong (fst meridian-chart) (merid (vertexSelection j (push k i))))
          (cong (coordinate j) (merid (push k i))))
        refl (selection-meridian-petal j k true) i

    meridian-selection : (j : Fin 2) (a : Susp (RoseProduct.Vertices 2))
      → fst meridian-chart (suspFun (vertexSelection j) a) ≡ coordinate j a
    meridian-selection j north = refl
    meridian-selection j south = refl
    meridian-selection j (merid a i) r = selection-meridian j a r i

    word-rose : (x : RoseProduct.Rose 2)
      → Words.word-chart (fst rose-chart x) ≡ x
    word-rose x =
      sym (retEq rose-chart (Words.word-chart (fst rose-chart x)))
      ∙ cong (invEq rose-chart)
          (cong fst (funExt⁻ word-marking-id (fst rose-chart x , 0C)))
      ∙ retEq rose-chart x

    meridian-marked : (j : Fin 2) (a : Susp (RoseProduct.Vertices 2))
      → fst meridian-chart (suspFun (vertexSelection j) a)
        ≡ circleToC (pickPetal j (Words.word-chart (fst base-chart a)))
    meridian-marked j a = meridian-selection j a
      ∙ sym (cong (circleToC ∘ pickPetal j)
          (word-rose (fst (RoseProduct.suspension-chart 2) a)))

import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

private
  torus-product : Chart.Product 1 → T²
  torus-product (a , b) = fst meridian-chart a , fst fibre-chart b

  core-product : Chart.Product 2 → Literal.Core
  core-product (a , b) = fst base-chart a , fst fibre-chart b

  suspension-product : Fin 2 → Chart.Product 2 → Chart.Product 1
  suspension-product j (a , b) = suspFun (vertexSelection j) a , b

  abstract
    wedge-product : (j : Fin 2) (w : RoseProduct.Wedge 2)
      → Path (Chart.Product 1) (⋁↪ (wedgeSelection j w))
          (suspension-product j (⋁↪ w))
    wedge-product j (inl a) = refl
    wedge-product j (inr b) = refl
    wedge-product j (push tt i) = refl

    lower-marked : (j : Fin 2) (x : SphereBouquet 1 (Fin 3))
      → fst torus-chart (inr (lower j x))
        ≡ ProjectH2.project j (fst core-chart (inr x))
    lower-marked j x =
      cong torus-product (Chart.on-edge 1 (lower j x))
      ∙ cong (torus-product ∘ ⋁↪)
          (retEq (RoseProduct.target-chart 1)
            (wedgeSelection j (invEq (RoseProduct.target-chart 2) x)))
      ∙ cong torus-product
          (wedge-product j (invEq (RoseProduct.target-chart 2) x))
      ∙ ΣPathP
          (meridian-marked j (fst (⋁↪ (invEq (RoseProduct.target-chart 2) x))) , refl)
      ∙ sym (cong (ProjectH2.project j ∘ core-product) (Chart.on-edge 2 x))

-- Work in the canonical stage Pushout αcell fst.  The lower homotopy
-- includes the actual sequence-map commutation path, not an assumption
-- that agreement on the 1-skeleton implies agreement everywhere.
module RealizationStage (j : Fin 2) where
  private
    F G : Pushout (cell-attaching 2) fst → T²
    F = fst torus-chart ∘ sparseTop j ∘ invEq (cell-attachment 2)
    G = ProjectH2.project j ∘ fst core-chart ∘ invEq (cell-attachment 2)

    abstract
      on-lower : (x : SphereBouquet 1 (Fin 3)) → F (inl x) ≡ G (inl x)
      on-lower x =
        cong (fst torus-chart) (sym (SparseStage.Stage.comm j x))
        ∙ cong (fst torus-chart) (cell-inclusion 1 (lower j x))
        ∙ lower-marked j x
        ∙ sym (cong (ProjectH2.project j ∘ fst core-chart) (cell-inclusion 2 x))

  abstract
    top-marked : (z : cofib (RoseProduct.attaching 2))
      → fst torus-chart (sparseTop j z)
        ≡ ProjectH2.project j (fst core-chart z)
    top-marked z =
      sym (cong (fst torus-chart ∘ sparseTop j) (retEq (cell-attachment 2) z))
      ∙ CircleAttachment.homotopy (cell-attaching 2)
          (isGroupoidΣ emsquash (λ _ → emsquash)) F G on-lower
          (fst (cell-attachment 2) z)
      ∙ cong (ProjectH2.project j ∘ fst core-chart) (retEq (cell-attachment 2) z)

abstract
  sparse-marked-agreement : (j : Fin 2) → SparseMarkedAgreement j
  sparse-marked-agreement j = funExt λ a →
    cong (realiseCellMap (sparseCellular j)) (funExt⁻ original-core-concrete a)
    ∙ sparseCellular-realise-top j (invEq core-chart a)
    ∙ cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1))))
        (sym (retEq torus-chart (sparseTop j (invEq core-chart a)))
          ∙ cong (invEq torus-chart)
              (RealizationStage.top-marked j (invEq core-chart a)
                ∙ cong (ProjectH2.project j) (secEq core-chart a)))
    ∙ sym (funExt⁻ original-torus-concrete (ProjectH2.project j a))

open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module GraphProduct ; torus-square-coordinate)
import DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse as Sparse

abstract
  project-H₂ : (j : Fin 2) (z : fst (H̃ᶜʷ graph×circleCW 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = graph×circleCW} {D = torusCW} 2 (ProjectH2.project j)) z)
      ≡ GraphProduct.square-coordinate z j
  project-H₂ j = Sparse.project-H₂ j (sparse-marked-agreement j)
