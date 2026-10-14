{-# OPTIONS --safe --cubical --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.Pieces where

-- Actual initial/base inner pieces. Chosen CW models are untruncated;
-- cell bounds certify stabilization of these exact selected skeleta,
-- retaining their chosen realization charts.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm)
open import Cubical.Data.Nat.Order.Inductive using (_≟ᵗ_ ; <→<ᵗ)
open import Cubical.Data.List.Base using (List)
open import Cubical.Data.Fin using (Fin ; ¬Fin0)
import Cubical.Data.SumFin as SF
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to inj₁ ; inr to inj₂)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sequence using (SequenceMap)
import Cubical.HITs.Bouquet.Base as Bouquet
open import Cubical.HITs.Bouquet.Properties using (Iso-SphereBouquet-Bouquet)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Pushout using (inl ; pushoutEquiv)
open import Cubical.HITs.Pushout.Properties using (PushoutEmptyFam)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.CW.Base using
  (CWskel ; CW↪ ; finCWskel ; finCW↑ ; hasCWskel ; realise ; module CWskel-fields)
open CWskel-fields using (card)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Strictification using (strictCWskel ; strictifyFame ; strict≡)
open import Cubical.CW.Instances.Empty using
  (CWskel⊥ ; finCWskel⊥ ; hasCWskel⊥)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
import Cubical.CW.Instances.SphereBouquetMap as SB
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; Finite≤ ; Hzero ; H̃ᶜʷ)
open import DeloopS3.Bridge.Recognition.HomologyDimension using
  (finite≤-homology-above)
import DeloopS3.Bridge.SpanCells as SpanCells
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
import DeloopS3.Bridge.ComponentHomology.ProductBoundary2 as ProductBoundary2
import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts as Concrete
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
open Input using (ShortCase)

-- No cells at a stage makes the inclusion of that selected skeleton stable.
abstract
  no-cells-stable : (K : CWskel ℓ-zero) (r : ℕ)
    → card K r ≡ 0 → isEquiv (CW↪ K r)
  no-cells-stable K r p = snd (compEquiv
    (isoToEquiv (PushoutEmptyFam (λ z → noFin (fst z)) noFin
      {f = CWskel-fields.α K r} {g = fst}))
    (invEquiv (CWskel-fields.e K r)))
    where
    noFin : Fin (card K r) → Empty.⊥
    noFin a = ¬Fin0 (subst Fin p a)

bounded-skeleton : (d : ℕ) (K : CWskel ℓ-zero)
  → ((k : ℕ) → card K (suc d + k) ≡ 0) → finCWskel ℓ-zero (suc d)
bounded-skeleton d K cells = fst K , snd K , λ k →
  no-cells-stable K (k + suc d)
    (cong (card K) (+-comm k (suc d)) ∙ cells k)

-- The two Fin presentations are related explicitly on petal indices.
module RoseAdapter (gs : List ℕ) where
  index : SF.Fin (P.length gs) ≃ Fin (P.length gs)
  index = SumFin≃Fin (P.length gs)

  roseIso : Iso (R.Rose gs) (Bouquet.Bouquet (Fin (P.length gs)))
  Iso.fun roseIso R.root = Bouquet.base
  Iso.fun roseIso (R.petal k i) = Bouquet.loop (equivFun index k) i
  Iso.inv roseIso Bouquet.base = R.root
  Iso.inv roseIso (Bouquet.loop k i) = R.petal (invEq index k) i
  Iso.sec roseIso Bouquet.base = refl
  Iso.sec roseIso (Bouquet.loop k i) j = Bouquet.loop (secEq index k j) i
  Iso.ret roseIso R.root = refl
  Iso.ret roseIso (R.petal k i) j = R.petal (retEq index k j) i

rose-bouquet : (gs : List ℕ) → R.Rose gs ≃ SphereBouquet 1 (Fin (P.length gs))
rose-bouquet gs = compEquiv (isoToEquiv (RoseAdapter.roseIso gs))
  (invEquiv (isoToEquiv Iso-SphereBouquet-Bouquet))

rose-product-chart : (gs : List ℕ)
  → (R.Rose gs × R.C) ≃ (RoseProduct.Rose (P.length gs) × S¹)
rose-product-chart gs = compEquiv
  (Σ-cong-equiv-fst {B = λ _ → R.C} (rose-bouquet gs))
  (Σ-cong-equiv-snd (λ _ → invEquiv S¹≃C))

rose-product-model : (gs : List ℕ) → hasCWskel (R.Rose gs × R.C)
rose-product-model gs = RoseProduct.skeleton (P.length gs) ,
  compEquiv (rose-product-chart gs) (snd (RoseProduct.has-skeleton (P.length gs)))

-- has-skeleton alone does not prove finiteness. The actual inclusion is
-- the convergent pushout inclusion followed by the inverse skeletal chart.
abstract
  rose-product-stable : (n k : ℕ)
    → isEquiv (CW↪ (RoseProduct.skeleton n) (k + 3))
  rose-product-stable n k = snd (compEquiv
    (inl , SB.SphereBouquet/ˢᵏᵉˡConverges n (suc n) (k + 3)
      (RoseProduct.attaching n) (<→<ᵗ (k , refl))
      ((k + 3) ≟ᵗ 1) ((k + 3) ≟ᵗ 2))
    (invEquiv (SB.SphereBouquet/EqGen n (suc n) (k + 3)
      (RoseProduct.attaching n) (suc (k + 3) ≟ᵗ 2)
      ((k + 3) ≟ᵗ 1) ((k + 3) ≟ᵗ 2))))

rose-product-finite-model : (n : ℕ) → finCWskel ℓ-zero 3
rose-product-finite-model n = fst (RoseProduct.skeleton n) ,
  snd (RoseProduct.skeleton n) , rose-product-stable n

rose-product-finite : (gs : List ℕ) → Finite≤ 2 (R.Rose gs × R.C)
rose-product-finite gs = PT.∣ rose-product-finite-model (P.length gs) ,
  snd (rose-product-model gs) ∣₁

-- Finite disjoint families, including the empty family. These charts use
-- SumFin, exactly the index in R.FaceIx; no cardinalities are guessed.
empty-product-iso : (X : Type₀) → Iso (SF.Fin 0 × X) Empty.⊥
Iso.fun (empty-product-iso X) (e , x) = e
Iso.inv (empty-product-iso X) ()
Iso.sec (empty-product-iso X) ()
Iso.ret (empty-product-iso X) (() , x)

split-product-iso : (n : ℕ) (X : Type₀)
  → Iso (SF.Fin (suc n) × X) (X ⊎ (SF.Fin n × X))
Iso.fun (split-product-iso n X) (SF.fzero , x) = inj₁ x
Iso.fun (split-product-iso n X) (SF.fsuc k , x) = inj₂ (k , x)
Iso.inv (split-product-iso n X) (inj₁ x) = SF.fzero , x
Iso.inv (split-product-iso n X) (inj₂ (k , x)) = SF.fsuc k , x
Iso.sec (split-product-iso n X) (inj₁ x) = refl
Iso.sec (split-product-iso n X) (inj₂ (k , x)) = refl
Iso.ret (split-product-iso n X) (SF.fzero , x) = refl
Iso.ret (split-product-iso n X) (SF.fsuc k , x) = refl

private
  empty1 : Finite≤ 1 Empty.⊥
  empty1 = PT.∣ finCW↑ 0 2 (2 , refl) finCWskel⊥ , snd hasCWskel⊥ ∣₁
  empty2 : Finite≤ 2 Empty.⊥
  empty2 = PT.∣ finCW↑ 0 3 (3 , refl) finCWskel⊥ , snd hasCWskel⊥ ∣₁

copies1-finite : (n : ℕ) {X : Type₀} → Finite≤ 1 X → Finite≤ 1 (SF.Fin n × X)
copies1-finite zero {X} f = SpanCells.finite-equiv 1
  (isoToEquiv (empty-product-iso X)) empty1
copies1-finite (suc n) {X} f = SpanCells.finite-equiv 1
  (isoToEquiv (split-product-iso n X)) (SpanCells.sum1-finite f (copies1-finite n f))

copies2-finite : (n : ℕ) {X : Type₀} → Finite≤ 2 X → Finite≤ 2 (SF.Fin n × X)
copies2-finite zero {X} f = SpanCells.finite-equiv 2
  (isoToEquiv (empty-product-iso X)) empty2
copies2-finite (suc n) {X} f = SpanCells.finite-equiv 2
  (isoToEquiv (split-product-iso n X)) (SpanCells.sum2-finite f (copies2-finite n f))

-- Chosen coproduct models are constructed, never extracted from PT.
model-equiv : {X Y : Type₀} → X ≃ Y → hasCWskel Y → hasCWskel X
model-equiv e (K , r) = K , compEquiv e r

private
  emptyCell : (K : CWskel ℓ-zero) → cellMap (strictCWskel CWskel⊥) (strictCWskel K)
  SequenceMap.map (emptyCell K) n x = Empty.rec (invEq (strictifyFame CWskel⊥ n) x)
  SequenceMap.comm (emptyCell K) n x = Empty.rec (invEq (strictifyFame CWskel⊥ n) x)

  strict-realization : {X : Type₀} (M : hasCWskel X)
    → X ≃ realise (strictCWskel (fst M))
  strict-realization M = compEquiv (snd M)
    (pathToEquiv (cong realise (sym (strict≡ (fst M)))))

module SumSkeleton (X Y : Type₀) (MX : hasCWskel X) (MY : hasCWskel Y) where
  module PO = CWPushout ℓ-zero CWskel⊥ (fst MX) (fst MY)
    (emptyCell (fst MX)) (emptyCell (fst MY))

  -- Keep cells transparent for later coefficient calculations; seal only
  -- the heavy equivalence of realizations.
  skeleton : CWskel ℓ-zero
  skeleton = PO.pushoutSkel

  abstract
    realization : (X ⊎ Y) ≃ realise skeleton
    realization = compEquiv (SpanCells.Disjoint.sumEquiv X Y)
      (compEquiv
        (pushoutEquiv (SpanCells.Disjoint.left X Y) (SpanCells.Disjoint.right X Y)
          (realiseCellMap {C = PO.B} {D = PO.C} PO.f)
          (realiseCellMap {C = PO.B} {D = PO.D} PO.g)
          (strict-realization hasCWskel⊥) (strict-realization MX) (strict-realization MY)
          (funExt λ e → Empty.rec e) (funExt λ e → Empty.rec e))
        (snd PO.hasCWskelPushout))

  model : hasCWskel (X ⊎ Y)
  model = skeleton , realization

  no-cells : (r : ℕ) → fst (snd (fst MX)) r ≡ 0
    → fst (snd (fst MY)) r ≡ 0 → fst (snd skeleton) r ≡ 0
  no-cells zero p q = cong₂ _+_ p q
  no-cells (suc r) p q = cong₂ (λ a b → (a + 0) + b) p q

copies-model : (n : ℕ) {X : Type₀} → hasCWskel X → hasCWskel (SF.Fin n × X)
copies-model zero {X} M = model-equiv (isoToEquiv (empty-product-iso X)) hasCWskel⊥
copies-model (suc n) {X} M = model-equiv (isoToEquiv (split-product-iso n X))
  (SumSkeleton.model X (SF.Fin n × X) M (copies-model n M))

triple-model : {X : Type₀} → hasCWskel X → hasCWskel (Ch.Kind × X)
triple-model {X} M = model-equiv (invEquiv (Input.tripleIndex X))
  (SumSkeleton.model (X ⊎ X) X (SumSkeleton.model X X M M) M)

copies-no-cells : (n : ℕ) {X : Type₀} (M : hasCWskel X) (r : ℕ)
  → card (fst M) r ≡ 0 → card (fst (copies-model n M)) r ≡ 0
copies-no-cells zero M r p = refl
copies-no-cells (suc n) {X} M r p =
  SumSkeleton.no-cells X (SF.Fin n × X) M (copies-model n M) r p
    (copies-no-cells n M r p)

triple-no-cells : {X : Type₀} (M : hasCWskel X) (r : ℕ)
  → card (fst M) r ≡ 0 → card (fst (triple-model M)) r ≡ 0
triple-no-cells {X} M r p =
  SumSkeleton.no-cells (X ⊎ X) X (SumSkeleton.model X X M M) M r
    (SumSkeleton.no-cells X X M M r p p) p

-- Public boundary-index adapter: the dependent Kind-indexed family is
-- not definitionally R.FaceIx, and it is not replaced by a three-element set.
Bdy : ShortCase → Type₀
Bdy c = Σ[ k ∈ Ch.Kind ] Input.Bd c k

boundary-index : (c : ShortCase) → Bdy c ≃ R.FaceIx (Input.S₀ c)
boundary-index = Input.allBoundaryIndex

initial-overlap-model : (c : ShortCase) → hasCWskel (R.O (Input.S₀ c))
initial-overlap-model c = copies-model (P.length (Ch.faces (Input.S₀ c)))
  Concrete.concrete-torus-skeleton

initial-left-model : (c : ShortCase) → hasCWskel (R.L (Input.S₀ c))
initial-left-model c = rose-product-model (Input.gs c)

initial-right-model : (c : ShortCase) → hasCWskel (R.R (Input.S₀ c))
initial-right-model c = copies-model (P.length (Ch.faces (Input.S₀ c)))
  Concrete.concrete-circle-skeleton

initial-overlap-cells : (c : ShortCase) (k : ℕ)
  → card (fst (initial-overlap-model c)) (3 + k) ≡ 0
initial-overlap-cells c k = copies-no-cells (P.length (Ch.faces (Input.S₀ c)))
  Concrete.concrete-torus-skeleton (3 + k) refl

initial-left-cells : (c : ShortCase) (k : ℕ)
  → card (fst (initial-left-model c)) (3 + k) ≡ 0
initial-left-cells c k = refl

initial-right-cells : (c : ShortCase) (k : ℕ)
  → card (fst (initial-right-model c)) (2 + k) ≡ 0
initial-right-cells c k = copies-no-cells (P.length (Ch.faces (Input.S₀ c)))
  Concrete.concrete-circle-skeleton (2 + k) refl

initial-overlap-finite : (c : ShortCase) → Finite≤ 2 (R.O (Input.S₀ c))
initial-overlap-finite c = copies2-finite (P.length (Ch.faces (Input.S₀ c)))
  SpanCells.torus-finite

initial-left-finite : (c : ShortCase) → Finite≤ 2 (R.L (Input.S₀ c))
initial-left-finite c = rose-product-finite (Input.gs c)

initial-right-finite : (c : ShortCase) → Finite≤ 1 (R.R (Input.S₀ c))
initial-right-finite c = copies1-finite (P.length (Ch.faces (Input.S₀ c)))
  SpanCells.circle-finite

base-overlap-model : (c : ShortCase) → hasCWskel (R.Span.O (Input.BaseSpan c))
base-overlap-model c = triple-model Concrete.concrete-torus-skeleton

-- The inverse literal span chart is followed by the Concrete core chart.
-- Thus the base-left marking is exactly the one used by Concrete cell maps.
base-left-model : (c : ShortCase) → hasCWskel (R.Span.L (Input.BaseSpan c))
base-left-model c = model-equiv
  (invEquiv (R.SpanEquiv.leftVertex (Input.originalSpanEquiv c)))
  Concrete.concrete-core-skeleton

base-right-model : (c : ShortCase) → hasCWskel (R.Span.R (Input.BaseSpan c))
base-right-model c = triple-model Concrete.concrete-circle-skeleton

base-overlap-cells : (c : ShortCase) (k : ℕ)
  → card (fst (base-overlap-model c)) (3 + k) ≡ 0
base-overlap-cells c k = triple-no-cells Concrete.concrete-torus-skeleton
  (3 + k) refl

base-left-cells : (c : ShortCase) (k : ℕ)
  → card (fst (base-left-model c)) (3 + k) ≡ 0
base-left-cells c k = refl

base-right-cells : (c : ShortCase) (k : ℕ)
  → card (fst (base-right-model c)) (2 + k) ≡ 0
base-right-cells c k = triple-no-cells Concrete.concrete-circle-skeleton
  (2 + k) refl

base-overlap-finite : (c : ShortCase) → Finite≤ 2 (R.Span.O (Input.BaseSpan c))
base-overlap-finite c = SpanCells.finite-equiv 2 (invEquiv (Input.tripleIndex R.T²))
  SpanCells.three-tori-finite

base-left-finite : (c : ShortCase) → Finite≤ 2 (R.Span.L (Input.BaseSpan c))
base-left-finite c = SpanCells.finite-equiv 2
  (invEquiv (R.SpanEquiv.leftVertex (Input.originalSpanEquiv c))) SpanCells.core-finite

base-right-finite : (c : ShortCase) → Finite≤ 1 (R.Span.R (Input.BaseSpan c))
base-right-finite c = SpanCells.finite-equiv 1 (invEquiv (Input.tripleIndex R.C))
  SpanCells.three-circles-finite

record FiniteCWSpan (D : R.Span ℓ-zero ℓ-zero ℓ-zero) : Type₁ where
  field
    overlap-model : hasCWskel (R.Span.O D)
    left-model : hasCWskel (R.Span.L D)
    right-model : hasCWskel (R.Span.R D)
    -- These cell bounds stabilize the exact selected skeleta at 3/3/2.
    overlap-cells : (k : ℕ) → card (fst overlap-model) (3 + k) ≡ 0
    left-cells : (k : ℕ) → card (fst left-model) (3 + k) ≡ 0
    right-cells : (k : ℕ) → card (fst right-model) (2 + k) ≡ 0

  overlap-finite-model : finCWskel ℓ-zero 3
  overlap-finite-model = bounded-skeleton 2 (fst overlap-model) overlap-cells

  left-finite-model : finCWskel ℓ-zero 3
  left-finite-model = bounded-skeleton 2 (fst left-model) left-cells

  right-finite-model : finCWskel ℓ-zero 2
  right-finite-model = bounded-skeleton 1 (fst right-model) right-cells

  overlap-finite : Finite≤ 2 (R.Span.O D)
  overlap-finite = PT.∣ overlap-finite-model , snd overlap-model ∣₁

  left-finite : Finite≤ 2 (R.Span.L D)
  left-finite = PT.∣ left-finite-model , snd left-model ∣₁

  right-finite : Finite≤ 1 (R.Span.R D)
  right-finite = PT.∣ right-finite-model , snd right-model ∣₁

  O-CW L-CW R-CW : CW₀
  O-CW = R.Span.O D , PT.∣ overlap-model ∣₁
  L-CW = R.Span.L D , PT.∣ left-model ∣₁
  R-CW = R.Span.R D , PT.∣ right-model ∣₁

  total-finite : Finite≤ 3 (R.Total D)
  total-finite = SpanCells.pushout-finite≤ (R.Span.left D) (R.Span.right D)
    2 2 1 overlap-finite left-finite right-finite

initial-pieces : (c : ShortCase) → FiniteCWSpan (R.diagram (Input.S₀ c))
initial-pieces c = record
  { overlap-model = initial-overlap-model c
  ; left-model = initial-left-model c
  ; right-model = initial-right-model c
  ; overlap-cells = initial-overlap-cells c
  ; left-cells = initial-left-cells c
  ; right-cells = initial-right-cells c }

base-pieces : (c : ShortCase) → FiniteCWSpan (Input.BaseSpan c)
base-pieces c = record
  { overlap-model = base-overlap-model c
  ; left-model = base-left-model c
  ; right-model = base-right-model c
  ; overlap-cells = base-overlap-cells c
  ; left-cells = base-left-cells c
  ; right-cells = base-right-cells c }

initial-finite : (c : ShortCase) → Finite≤ 3 (R.T (Input.S₀ c))
initial-finite c = FiniteCWSpan.total-finite (initial-pieces c)

base-finite : (c : ShortCase) → Finite≤ 3 (Input.M_G c)
base-finite c = FiniteCWSpan.total-finite (base-pieces c)

O₀CW L₀CW R₀CW OᵦCW LᵦCW RᵦCW : ShortCase → CW₀
O₀CW c = FiniteCWSpan.O-CW (initial-pieces c)
L₀CW c = FiniteCWSpan.L-CW (initial-pieces c)
R₀CW c = FiniteCWSpan.R-CW (initial-pieces c)
OᵦCW c = FiniteCWSpan.O-CW (base-pieces c)
LᵦCW c = FiniteCWSpan.L-CW (base-pieces c)
RᵦCW c = FiniteCWSpan.R-CW (base-pieces c)

-- Vanishing concerns homology of the actual CW₀ values, independently of
-- which finite skeleton witnesses the bound. No PT witness is extracted.
initial-left-H₃-zero : (c : ShortCase) → Hzero (L₀CW c) 3
initial-left-H₃-zero c = finite≤-homology-above (L₀CW c) 2 3
  (initial-left-finite c) (0 , refl)

initial-right-H₃-zero : (c : ShortCase) → Hzero (R₀CW c) 3
initial-right-H₃-zero c = finite≤-homology-above (R₀CW c) 1 3
  (initial-right-finite c) (1 , refl)

initial-right-H₂-zero : (c : ShortCase) → Hzero (R₀CW c) 2
initial-right-H₂-zero c = finite≤-homology-above (R₀CW c) 1 2
  (initial-right-finite c) (0 , refl)

base-left-H₃-zero : (c : ShortCase) → Hzero (LᵦCW c) 3
base-left-H₃-zero c = finite≤-homology-above (LᵦCW c) 2 3
  (base-left-finite c) (0 , refl)

base-right-H₃-zero : (c : ShortCase) → Hzero (RᵦCW c) 3
base-right-H₃-zero c = finite≤-homology-above (RᵦCW c) 1 3
  (base-right-finite c) (1 , refl)

base-right-H₂-zero : (c : ShortCase) → Hzero (RᵦCW c) 2
base-right-H₂-zero c = finite≤-homology-above (RᵦCW c) 1 2
  (base-right-finite c) (0 , refl)

-- These coordinates use precisely the selected left realization.
-- No identification with the other opaque torus/core markings is asserted.
module InitialLeft (c : ShortCase) = ProductBoundary2.MarkedProduct
  (P.length (Input.gs c)) (L₀CW c) (snd (initial-left-model c))
module BaseLeft (c : ShortCase) = ProductBoundary2.MarkedProduct
  2 (LᵦCW c) (snd (base-left-model c))

initial-left-H₂ : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (L₀CW c) 2) (AbGroup→Group ℤ[Fin (P.length (Input.gs c)) ])
initial-left-H₂ c = InitialLeft.H₂ c

base-left-H₂ : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (LᵦCW c) 2) (AbGroup→Group ℤ[Fin 2 ])
base-left-H₂ c = BaseLeft.H₂ c

initial-left-generators : (c : ShortCase)
  → Fin (P.length (Input.gs c)) → fst (H̃ᶜʷ (L₀CW c) 2)
initial-left-generators c = InitialLeft.square-generator c

base-left-generators : (c : ShortCase) → Fin 2 → fst (H̃ᶜʷ (LᵦCW c) 2)
base-left-generators c = BaseLeft.square-generator c
