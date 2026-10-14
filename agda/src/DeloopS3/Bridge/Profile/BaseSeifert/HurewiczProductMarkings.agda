{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.HurewiczProductMarkings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
import Cubical.HITs.SequentialColimit as SC
open import Cubical.CW.Base using (realise ; CW↪)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ ; hasCWskelSphere)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.Profile.BaseSeifert.HurewiczChartProof.EdgeCircle using (module Edge)
import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Skeletons as Facts
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.Data.Int using (ℤ ; pos ; isSetℤ)
open import Cubical.Data.Sigma using (Σ≡Prop)
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤFinGenerator)
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→ ; H̃ᶜʷ→)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using
  (chosen-skeleton ; chosen-skeleton-path)
open import DeloopS3.Bridge.DegreeSpan.WitnessTransport using
  (witness-comparison ; witness-comparison-action ; witness-comparison-natural)
import DeloopS3.Bridge.ComponentHomology.CircleCofibre
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Groups using
  (module ProductGroups ; module MarkedProduct)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.Susp using (north)
open import Cubical.HITs.Wedge using (⋁↪ ; Iso-⋁genFinSuc-⋁genFin⋁)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (torus-chart ; core-chart ; meridian-chart ; base-chart ; fibre-chart ; rose-chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Products using
  (original-torus-concrete ; original-core-concrete)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (torus-skeleton ; graph×circle-skeleton)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module TorusProduct ; module GraphProduct)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC ; hC)
open import DeloopS3.Move.CancelMinimal using (T² ; C ; 0C)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass using
  (loop-class ; loop-rebase)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.WordPaths using
  (torus-base ; torus-u ; torus-h ; core-base ; core-base₂ ; core-a ; core-b ; core-h
  ; core-edge ; boundary₂-u-conjugate)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components using
  (core-a-class ; core-b-class ; core-h-class)
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group using (Group₀ ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass using (loop-natural)
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components as Components
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Assembly as Assembly
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Generators using
  (e-u1 ; e-u2 ; e-u3 ; e-h1 ; e-h2 ; e-h3)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof using
  (module Actual ; HurewiczChartIdentification ; DegreeOneStatement ; degree-one-proof)
open import DeloopS3.Bridge.Profile.BaseSeifert.HurewiczChartProof using
  (filling-1-coordinate ; filling-2-coordinate ; filling-3-coordinate)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (overlapCW ; fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates using
  (tori₂ ; module TwoTori ; module ThreeTori ; overlap-merge ; overlap-H₁
  ; overlap-H₁-on-components ; fillings-H₁ ; vertices-H₁ ; vertices-H₁-eval)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (map-square)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ⁶ ; vertex₁)

-- Keep the attachment and both finite ranks abstract while checking the
-- stage-2 to stage-3 path: no product chart is normalized in this lemma.
module EdgeRealization {m n : ℕ} (α : FinSphereBouquetMap m n 0) (k : Fin n) where
  private
    T = SphereBouquet/ˢᵏᵉˡ α

  abstract
    on-circle : (x : S¹)
      → Path (realise T)
          (Edge.realization α k (fst (snd (hasCWskelSphere 1)) x))
          (fst (snd (hasCWskelSphereBouquet/ α)) (inr (inr (k , x))))
    on-circle x = SC.push (inr (k , x))
      ∙ cong (SC.incl {n = 3}) (Facts.Bouquet.edge α (inr (k , x)))

    conjugated : (fst (snd (hasCWskelSphereBouquet/ α))
        ∘ (λ x → inr (inr (k , x))) ∘ invEq (snd (hasCWskelSphere 1)))
      ≡ Edge.realization α k
    conjugated = funExt λ x →
      sym (on-circle (invEq (snd (hasCWskelSphere 1)) x))
      ∙ cong (Edge.realization α k) (secEq (snd (hasCWskelSphere 1)) x)

private
  abstract
    witness-self : {A : Type} (s : hasCWskel A) (k : ℕ)
      (x : fst (H̃ˢᵏᵉˡ (fst s) k))
      → fst (fst (witness-comparison (A , PT.∣ s ∣₁) s k)) x ≡ x
    witness-self {A} s k x = witness-comparison-action (A , PT.∣ s ∣₁) s k x
      ∙ cong (λ p → transport (λ i → fst (H̃ᶜʷ (A , p i) k)) x)
          (isProp→isSet PT.squash₁ PT.∣ s ∣₁ PT.∣ s ∣₁
            (PT.squash₁ PT.∣ s ∣₁ PT.∣ s ∣₁) refl)
      ∙ transportRefl x

    chosen-circle-image : (X : CW₀) (s : hasCWskel (fst X)) (f : S¹ → fst X)
      → fst (fst (chosen-skeleton X s 1))
          (fst (cellular-map (Sᶜʷ 1) X 1 f) (genHₙSⁿ 0))
        ≡ fst (H̃ˢᵏᵉˡ→ {C = Sˢᵏᵉˡ 1} {D = fst s} 1
            (fst (snd s) ∘ f ∘ invEq (snd (hasCWskelSphere 1)))) (genHₙSⁿ 0)
    chosen-circle-image X s f =
      cong (λ e → fst (fst e) (fst (cellular-map (Sᶜʷ 1) X 1 f) (genHₙSⁿ 0)))
        (chosen-skeleton-path X s 1)
      ∙ cong (λ h → fst (fst (witness-comparison X s 1)) (fst h (genHₙSⁿ 0)))
          (cellular-map-agrees (Sᶜʷ 1) X 1 f)
      ∙ witness-comparison-natural (Sᶜʷ 1) X (hasCWskelSphere 1) s 1 f (genHₙSⁿ 0)
      ∙ cong (fst (H̃ˢᵏᵉˡ→ {C = Sˢᵏᵉˡ 1} {D = fst s} 1
          (fst (snd s) ∘ f ∘ invEq (snd (hasCWskelSphere 1)))))
          (witness-self (hasCWskelSphere 1) 1 (genHₙSⁿ 0))

module ProductEdge (n : ℕ) (X : CW₀)
  (e : fst X ≃ realise (RoseProduct.skeleton n)) where
  private
    α = RoseProduct.attaching n
    T = RoseProduct.skeleton n
    s : hasCWskel (fst X)
    s = T , e

  abstract
    cycle-is-edge : (k : Fin (suc n))
      → genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ α k ≡ ProductGroups.edge-cell n k
    cycle-is-edge k = cong SQ.[_]
      (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _) refl)
      ∙ sym (ProductGroups.edge-cell-compute n k)

    circle-coordinate : (k : Fin (suc n)) (f : S¹ → fst X)
      → ((x : S¹) → fst e (f x)
          ≡ fst (snd (hasCWskelSphereBouquet/ α)) (inr (inr (k , x))))
      → MarkedProduct.edge-coordinate n X e
          (fst (cellular-map (Sᶜʷ 1) X 1 f) (genHₙSⁿ 0)) ≡ ℤFinGenerator k
    circle-coordinate k f square =
      MarkedProduct.edge-coordinate-factor n X e _
      ∙ cong (Iso.fun (fst (ProductGroups.edge-iso n)))
          (chosen-circle-image X s f
          ∙ cong (λ g → fst (H̃ˢᵏᵉˡ→ {C = Sˢᵏᵉˡ 1} {D = T} 1 g) (genHₙSⁿ 0))
              (funExt (λ x → square (invEq (snd (hasCWskelSphere 1)) x))
              ∙ EdgeRealization.conjugated α k)
          ∙ Edge.homology-generator α k
          ∙ cycle-is-edge k)
      ∙ ProductGroups.edge-cell-coordinate n k

-- Inverting the target wedge chart one edge at a time avoids normalizing
-- the Whitehead-product equivalence.  Both equations are unpointed.
module EdgeCharts (n : ℕ) where
  open RoseProduct n
  abstract
    rose-inverse : (k : Fin n) (x : S¹)
      → invEq target-chart (inr (fsuc k , x))
        ≡ inl (invEq suspension-chart (inr (k , x)))
    rose-inverse k x =
      sym (cong (invEq target-chart)
        (cong (λ z → Iso.inv (Iso-⋁genFinSuc-⋁genFin⋁
            {n = n} {A = λ _ → S¹ , base}) (inl z))
          (secEq suspension-chart (inr (k , x)))))
      ∙ retEq target-chart (inl (invEq suspension-chart (inr (k , x))))

    fibre-inverse : (x : S¹)
      → invEq target-chart (inr (fzero , x)) ≡ inr (invEq circle-chart x)
    fibre-inverse x = sym (cong (invEq target-chart)
        (cong {A = S¹} {B = λ _ → SphereBouquet 1 (Fin (suc n))}
          (λ z → inr (fzero , z)) (secEq circle-chart x)))
      ∙ retEq target-chart (inr (invEq circle-chart x))

    rose-top : (k : Fin n) (x : S¹)
      → fst (Chart.top-chart n) (inr (inr (fsuc k , x)))
        ≡ (invEq suspension-chart (inr (k , x)) , north)
    rose-top k x = Chart.on-edge n (inr (fsuc k , x))
      ∙ cong ⋁↪ (rose-inverse k x)

    fibre-top : (x : S¹)
      → fst (Chart.top-chart n) (inr (inr (fzero , x)))
        ≡ (north , invEq circle-chart x)
    fibre-top x = Chart.on-edge n (inr (fzero , x))
      ∙ cong ⋁↪ (fibre-inverse x)

private
  abstract
    circle-loop-image : (X : CW₀) (f : S¹ → fst X)
      → loop-class X (f base) (cong f loop)
        ≡ fst (cellular-map (Sᶜʷ 1) X 1 f) (genHₙSⁿ 0)
    circle-loop-image X f = cong
      (λ g → fst (cellular-map (Sᶜʷ 1) X 1 g) (genHₙSⁿ 0))
      (funExt λ { base → refl ; (loop i) → refl })

module ChartCoordinate (n : ℕ) (X : CW₀)
  (e : fst X ≃ realise (RoseProduct.skeleton n))
  (chart : cofib (RoseProduct.attaching n) ≃ fst X)
  (agreement : fst e ≡ fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching n)))
      ∘ invEq chart) where
  abstract
    loop-coordinate : (k : Fin (suc n)) (f : S¹ → fst X)
      → ((x : S¹) → fst chart (inr (inr (k , x))) ≡ f x)
      → MarkedProduct.edge-coordinate n X e (loop-class X (f base) (cong f loop))
        ≡ ℤFinGenerator k
    loop-coordinate k f forward =
      cong (MarkedProduct.edge-coordinate n X e) (circle-loop-image X f)
      ∙ ProductEdge.circle-coordinate n X e k f λ x →
          funExt⁻ agreement (f x)
          ∙ cong (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching n))))
              (cong (invEq chart) (sym (forward x)) ∙ retEq chart (inr (inr (k , x))))

-- The second core circle is based at d₂ 0C, not at p₀.
torus-u-circle torus-h-circle : S¹ → T²
torus-u-circle x = circleToC x , 0C
torus-h-circle x = 0C , circleToC x

core-a-circle core-b-circle core-h₂-circle : S¹ → Literal.Core
core-a-circle x = Literal.d₁ (circleToC x) , 0C
core-b-circle x = Literal.d₂ (circleToC x) , 0C
core-h₂-circle x = Literal.d₂ 0C , circleToC x

abstract
  torus-u-chart : (x : S¹)
    → fst torus-chart (inr (inr (fsuc fzero , x))) ≡ torus-u-circle x
  torus-u-chart x =
    cong (λ (z : Chart.Product 1) → fst meridian-chart (fst z) , fst fibre-chart (snd z))
      (EdgeCharts.rose-top 1 fzero x)
    ∙ ΣPathP (cong (λ z → circleToC
        (DeloopS3.Bridge.ComponentHomology.CircleCofibre.one-petal z))
        (secEq (RoseProduct.suspension-chart 1) (inr (fzero , x))) , refl)

  torus-h-chart : (x : S¹)
    → fst torus-chart (inr (inr (fzero , x))) ≡ torus-h-circle x
  torus-h-chart x =
    cong (λ (z : Chart.Product 1) → fst meridian-chart (fst z) , fst fibre-chart (snd z))
      (EdgeCharts.fibre-top 1 x)
    ∙ ΣPathP (refl , cong circleToC (secEq (RoseProduct.circle-chart 1) x))

  core-rose-chart : (k : Fin 2) (x : S¹)
    → fst core-chart (inr (inr (fsuc k , x))) ≡ (fst rose-chart (inr (k , x)) , 0C)
  core-rose-chart k x =
    cong (λ (z : Chart.Product 2) → fst base-chart (fst z) , fst fibre-chart (snd z))
      (EdgeCharts.rose-top 2 k x)
    ∙ ΣPathP (cong (fst rose-chart)
        (secEq (RoseProduct.suspension-chart 2) (inr (k , x))) , refl)

  core-h₂-chart : (x : S¹)
    → fst core-chart (inr (inr (fzero , x))) ≡ core-h₂-circle x
  core-h₂-chart x =
    cong (λ (z : Chart.Product 2) → fst base-chart (fst z) , fst fibre-chart (snd z))
      (EdgeCharts.fibre-top 2 x)
    ∙ ΣPathP (refl , cong circleToC (secEq (RoseProduct.circle-chart 2) x))

private
  module TC = ChartCoordinate 1 torusCW (snd torus-skeleton)
    torus-chart original-torus-concrete
  module GC = ChartCoordinate 2 graph×circleCW (snd graph×circle-skeleton)
    core-chart original-core-concrete

abstract
  torus-u-coordinate : TorusProduct.edge-coordinate (loop-class torusCW torus-base torus-u)
    ≡ ℤFinGenerator (fsuc fzero)
  torus-u-coordinate = TC.loop-coordinate (fsuc fzero) torus-u-circle torus-u-chart

  torus-h-coordinate : TorusProduct.edge-coordinate (loop-class torusCW torus-base torus-h)
    ≡ ℤFinGenerator fzero
  torus-h-coordinate = TC.loop-coordinate fzero torus-h-circle torus-h-chart

  core-a-coordinate : GraphProduct.edge-coordinate core-a-class ≡ ℤFinGenerator (fsuc fzero)
  core-a-coordinate = GC.loop-coordinate (fsuc fzero) core-a-circle (core-rose-chart fzero)

  core-b-coordinate : GraphProduct.edge-coordinate core-b-class ≡ ℤFinGenerator (fsuc (fsuc fzero))
  core-b-coordinate = cong GraphProduct.edge-coordinate
      (cong (loop-class graph×circleCW core-base) (sym boundary₂-u-conjugate)
      ∙ loop-rebase graph×circleCW core-base core-base₂ core-edge
          (cong Literal.boundary₂ torus-u))
    ∙ GC.loop-coordinate (fsuc (fsuc fzero)) core-b-circle (core-rose-chart (fsuc fzero))

  core-h-coordinate : GraphProduct.edge-coordinate core-h-class ≡ ℤFinGenerator fzero
  core-h-coordinate = cong GraphProduct.edge-coordinate
      (λ i → loop-class graph×circleCW (Literal.edge i , 0C) (λ j → Literal.edge i , hC j))
    ∙ GC.loop-coordinate fzero core-h₂-circle core-h₂-chart

private
  open IsGroupHom using (pres1)

  -- Canonical coproduct inclusions, using the sum-equiv-eval beta.
  module Merge (G H K : Group₀) (L : GroupHom G K) (R : GroupHom H K)
    (merge : fst G × fst H → fst K)
    (beta : (x : fst G) (y : fst H)
      → merge (x , y) ≡ GroupStr._·_ (snd K) (fst L x) (fst R y)) where
    abstract
      left : (x : fst G) → merge (x , GroupStr.1g (snd H)) ≡ fst L x
      left x = beta x (GroupStr.1g (snd H))
        ∙ cong (GroupStr._·_ (snd K) (fst L x)) (pres1 (snd R))
        ∙ GroupStr.·IdR (snd K) (fst L x)

      right : (y : fst H) → merge (GroupStr.1g (snd G) , y) ≡ fst R y
      right y = beta (GroupStr.1g (snd G)) y
        ∙ cong (λ x → GroupStr._·_ (snd K) x (fst R y)) (pres1 (snd L))
        ∙ GroupStr.·IdL (snd K) (fst R y)

  module TwoBeta = Merge (H̃ᶜʷ torusCW 1) (H̃ᶜʷ torusCW 1) (H̃ᶜʷ tori₂ 1)
    (cellular-map torusCW tori₂ 1 Sum.inl)
    (cellular-map torusCW tori₂ 1 Sum.inr)
    (equivFun (fst (TwoTori.sum-equiv 0 (3 , refl))))
    (TwoTori.sum-equiv-eval 0 (3 , refl))

  module ThreeBeta = Merge (H̃ᶜʷ tori₂ 1) (H̃ᶜʷ torusCW 1) (H̃ᶜʷ overlapCW 1)
    (cellular-map tori₂ overlapCW 1 Sum.inl)
    (cellular-map torusCW overlapCW 1 Sum.inr)
    (equivFun (fst (ThreeTori.sum-equiv 0 (3 , refl))))
    (ThreeTori.sum-equiv-eval 0 (3 , refl))

  torus-zero : fst (H̃ᶜʷ torusCW 1)
  torus-zero = GroupStr.1g (snd (H̃ᶜʷ torusCW 1))

  filling-zero : fst (H̃ᶜʷ fillingsCW 1)
  filling-zero = GroupStr.1g (snd (H̃ᶜʷ fillingsCW 1))

  abstract
    merge-torus-1 : (x : fst (H̃ᶜʷ torusCW 1))
      → overlap-merge 0 (3 , refl) x torus-zero torus-zero
        ≡ fst (cellular-map torusCW overlapCW 1 Components.t1) x
    merge-torus-1 x =
      ThreeBeta.left (equivFun (fst (TwoTori.sum-equiv 0 (3 , refl))) (x , torus-zero))
      ∙ cong (fst (cellular-map tori₂ overlapCW 1 Sum.inl)) (TwoBeta.left x)
      ∙ map-square torusCW tori₂ overlapCW 1 Sum.inl Sum.inl Components.t1 refl x

    merge-torus-2 : (x : fst (H̃ᶜʷ torusCW 1))
      → overlap-merge 0 (3 , refl) torus-zero x torus-zero
        ≡ fst (cellular-map torusCW overlapCW 1 Components.t2) x
    merge-torus-2 x =
      ThreeBeta.left (equivFun (fst (TwoTori.sum-equiv 0 (3 , refl))) (torus-zero , x))
      ∙ cong (fst (cellular-map tori₂ overlapCW 1 Sum.inl)) (TwoBeta.right x)
      ∙ map-square torusCW tori₂ overlapCW 1 Sum.inr Sum.inl Components.t2 refl x

    merge-torus-3 : (x : fst (H̃ᶜʷ torusCW 1))
      → overlap-merge 0 (3 , refl) torus-zero torus-zero x
        ≡ fst (cellular-map torusCW overlapCW 1 Components.t3) x
    merge-torus-3 x =
      cong (λ y → equivFun (fst (ThreeTori.sum-equiv 0 (3 , refl))) (y , x))
        (TwoBeta.left torus-zero ∙ pres1 (snd (cellular-map torusCW tori₂ 1 Sum.inl)))
      ∙ ThreeBeta.right x

    torus-zero-coordinate : TorusProduct.edge-coordinate torus-zero ≡ (λ _ → pos 0)
    torus-zero-coordinate = pres1
      {A = fst (H̃ᶜʷ torusCW 1)} {B = Fin 2 → ℤ}
      {M = snd (H̃ᶜʷ torusCW 1)} {f = TorusProduct.edge-coordinate}
      {N = snd (AbGroup→Group ℤ[Fin 2 ])} (snd TorusProduct.H₁)

    filling-zero-coordinate : equivFun (fst fillings-H₁) filling-zero ≡ (pos 0 , pos 0 , pos 0)
    filling-zero-coordinate = pres1 (snd fillings-H₁)

  pack-edges : (Fin 2 → ℤ) → (Fin 2 → ℤ) → (Fin 2 → ℤ) → fst ℤ⁶
  pack-edges x y z = (x (fsuc fzero) , y (fsuc fzero) , z (fsuc fzero)) ,
    (x fzero , y fzero , z fzero)

  abstract
    overlap-loop-1 : (p : torus-base ≡ torus-base) (v : Fin 2 → ℤ)
      → TorusProduct.edge-coordinate (loop-class torusCW torus-base p) ≡ v
      → equivFun (fst overlap-H₁)
          (loop-class overlapCW (Components.t1 torus-base) (cong Components.t1 p))
        ≡ pack-edges v (λ _ → pos 0) (λ _ → pos 0)
    overlap-loop-1 p v coordinate =
      cong (equivFun (fst overlap-H₁))
        (sym (loop-natural torusCW overlapCW Components.t1 torus-base p)
        ∙ sym (merge-torus-1 (loop-class torusCW torus-base p)))
      ∙ overlap-H₁-on-components (loop-class torusCW torus-base p) torus-zero torus-zero
      ∙ (λ i → pack-edges (coordinate i) (torus-zero-coordinate i) (torus-zero-coordinate i))

    overlap-loop-2 : (p : torus-base ≡ torus-base) (v : Fin 2 → ℤ)
      → TorusProduct.edge-coordinate (loop-class torusCW torus-base p) ≡ v
      → equivFun (fst overlap-H₁)
          (loop-class overlapCW (Components.t2 torus-base) (cong Components.t2 p))
        ≡ pack-edges (λ _ → pos 0) v (λ _ → pos 0)
    overlap-loop-2 p v coordinate =
      cong (equivFun (fst overlap-H₁))
        (sym (loop-natural torusCW overlapCW Components.t2 torus-base p)
        ∙ sym (merge-torus-2 (loop-class torusCW torus-base p)))
      ∙ overlap-H₁-on-components torus-zero (loop-class torusCW torus-base p) torus-zero
      ∙ (λ i → pack-edges (torus-zero-coordinate i) (coordinate i) (torus-zero-coordinate i))

    overlap-loop-3 : (p : torus-base ≡ torus-base) (v : Fin 2 → ℤ)
      → TorusProduct.edge-coordinate (loop-class torusCW torus-base p) ≡ v
      → equivFun (fst overlap-H₁)
          (loop-class overlapCW (Components.t3 torus-base) (cong Components.t3 p))
        ≡ pack-edges (λ _ → pos 0) (λ _ → pos 0) v
    overlap-loop-3 p v coordinate =
      cong (equivFun (fst overlap-H₁))
        (sym (loop-natural torusCW overlapCW Components.t3 torus-base p)
        ∙ sym (merge-torus-3 (loop-class torusCW torus-base p)))
      ∙ overlap-H₁-on-components torus-zero torus-zero (loop-class torusCW torus-base p)
      ∙ (λ i → pack-edges (torus-zero-coordinate i) (torus-zero-coordinate i) (coordinate i))

    core-vertex-coordinate : (x : fst (H̃ᶜʷ graph×circleCW 1)) (v : Fin 3 → ℤ)
      → GraphProduct.edge-coordinate x ≡ v
      → fst Actual.core-coordinate x ≡ ((v (fsuc fzero) , v (fsuc (fsuc fzero))) ,
          v fzero , pos 0 , pos 0 , pos 0)
    core-vertex-coordinate x v coordinate = vertices-H₁-eval x filling-zero
      ∙ (λ i → ((coordinate i (fsuc fzero) , coordinate i (fsuc (fsuc fzero))) ,
          coordinate i fzero , filling-zero-coordinate i))

abstract
  source-u1-coordinate : equivFun (fst overlap-H₁) Components.source-u1 ≡ e-u1
  source-u1-coordinate = overlap-loop-1 torus-u (ℤFinGenerator (fsuc fzero)) torus-u-coordinate

  source-u2-coordinate : equivFun (fst overlap-H₁) Components.source-u2 ≡ e-u2
  source-u2-coordinate = overlap-loop-2 torus-u (ℤFinGenerator (fsuc fzero)) torus-u-coordinate

  source-u3-coordinate : equivFun (fst overlap-H₁) Components.source-u3 ≡ e-u3
  source-u3-coordinate = overlap-loop-3 torus-u (ℤFinGenerator (fsuc fzero)) torus-u-coordinate

  source-h1-coordinate : equivFun (fst overlap-H₁) Components.source-h1 ≡ e-h1
  source-h1-coordinate = overlap-loop-1 torus-h (ℤFinGenerator fzero) torus-h-coordinate

  source-h2-coordinate : equivFun (fst overlap-H₁) Components.source-h2 ≡ e-h2
  source-h2-coordinate = overlap-loop-2 torus-h (ℤFinGenerator fzero) torus-h-coordinate

  source-h3-coordinate : equivFun (fst overlap-H₁) Components.source-h3 ≡ e-h3
  source-h3-coordinate = overlap-loop-3 torus-h (ℤFinGenerator fzero) torus-h-coordinate

  core-a-vertex-coordinate : fst Actual.core-coordinate core-a-class ≡ Assembly.e-a
  core-a-vertex-coordinate = core-vertex-coordinate core-a-class (ℤFinGenerator (fsuc fzero)) core-a-coordinate

  core-b-vertex-coordinate : fst Actual.core-coordinate core-b-class ≡ Assembly.e-b
  core-b-vertex-coordinate = core-vertex-coordinate core-b-class (ℤFinGenerator (fsuc (fsuc fzero))) core-b-coordinate

  core-h-vertex-coordinate : fst Actual.core-coordinate core-h-class ≡ Assembly.e-h
  core-h-vertex-coordinate = core-vertex-coordinate core-h-class (ℤFinGenerator fzero) core-h-coordinate

  hurewicz-chart-identification : HurewiczChartIdentification
  Actual.Markings.source-u1 hurewicz-chart-identification = source-u1-coordinate
  Actual.Markings.source-u2 hurewicz-chart-identification = source-u2-coordinate
  Actual.Markings.source-u3 hurewicz-chart-identification = source-u3-coordinate
  Actual.Markings.source-h1 hurewicz-chart-identification = source-h1-coordinate
  Actual.Markings.source-h2 hurewicz-chart-identification = source-h2-coordinate
  Actual.Markings.source-h3 hurewicz-chart-identification = source-h3-coordinate
  Actual.Markings.core-a hurewicz-chart-identification = core-a-vertex-coordinate
  Actual.Markings.core-b hurewicz-chart-identification = core-b-vertex-coordinate
  Actual.Markings.core-h hurewicz-chart-identification = core-h-vertex-coordinate
  Actual.Markings.filling-1 hurewicz-chart-identification = filling-1-coordinate (pos 1)
  Actual.Markings.filling-2 hurewicz-chart-identification = filling-2-coordinate (pos 1)
  Actual.Markings.filling-3 hurewicz-chart-identification = filling-3-coordinate (pos 1)

  degree-one-unconditional : (p q r : ℤ) → DegreeOneStatement p q r
  degree-one-unconditional = degree-one-proof hurewicz-chart-identification
