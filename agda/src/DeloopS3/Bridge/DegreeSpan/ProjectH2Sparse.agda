{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse where

-- Sparse cellular maps on the RoseProduct skeleta, with computed quotient degrees.
-- The H₂ adapter takes marked realization agreement, supplied by ProjectH2Realization.

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq ; retEq ; secEq)
open import Cubical.Foundations.GroupoidLaws using (cong-∙ ; cong-∙∙)
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Fin using (Fin ; fzero)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Susp using (Susp ; north ; merid ; suspFun ; toSusp)
import Cubical.HITs.Join as Join
open Join using (join)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import DeloopS3.Bridge.CellularPushout.Cellular using (restrictCell)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; graph×circle-skeleton ; torus-skeleton)
open import Cubical.CW.Base using (module CWskel-fields ; cofibCW)
open import Cubical.Data.Sequence using (SequenceMap)
import DeloopS3.Bridge.DegreeSpan.ProjectH2 as ProjectH2

selected : Fin 2 → Fin 2 → Bool
selected (zero , _) (zero , _) = true
selected (zero , _) (suc zero , _) = false
selected (suc zero , _) (zero , _) = false
selected (suc zero , _) (suc zero , _) = true
selected (suc (suc n) , ()) _
selected _ (suc (suc n) , ())

private
  selectedVertex : Bool → Bool → RoseProduct.Vertices 1
  selectedVertex true b = inr (fzero , b)
  selectedVertex false b = inl tt

  selectedPush : (s : Bool)
    → Path (RoseProduct.Vertices 1) (inl tt) (selectedVertex s true)
  selectedPush true = push fzero
  selectedPush false = refl

vertexSelection : Fin 2 → RoseProduct.Vertices 2 → RoseProduct.Vertices 1
vertexSelection j (inl tt) = inl tt
vertexSelection j (inr (k , b)) = selectedVertex (selected j k) b
vertexSelection j (push k i) = selectedPush (selected j k) i

abstract
  vertexSelection-point : (j : Fin 2)
    → Path (RoseProduct.Vertices 1) (vertexSelection j (inl tt)) (inl tt)
  vertexSelection-point j = refl

joinSelection : Fin 2 → join (RoseProduct.Vertices 2) Bool
  → join (RoseProduct.Vertices 1) Bool
joinSelection j (Join.inl a) = Join.inl (vertexSelection j a)
joinSelection j (Join.inr b) = Join.inr b
joinSelection j (Join.push a b i) = Join.push (vertexSelection j a) b i

wedgeSelection : Fin 2 → RoseProduct.Wedge 2 → RoseProduct.Wedge 1
wedgeSelection j (inl a) = inl (suspFun (vertexSelection j) a)
wedgeSelection j (inr b) = inr b
wedgeSelection j (push tt i) = push tt i

abstract
  natural-push : (j : Fin 2) (a : RoseProduct.Vertices 2) (b : Bool)
    → Path (Path (RoseProduct.Wedge 1) (inr north) (inl north))
        (cong (wedgeSelection j)
          (cong (RoseProduct.W 2) (Join.push a b)))
        (cong (RoseProduct.W 1) (Join.push (vertexSelection j a) b))
  natural-push j a b =
    cong-∙∙ (wedgeSelection j)
      (λ i → inr (toSusp (Bool , true) b i))
      (sym (push tt))
      (λ i → inl (toSusp (RoseProduct.Vertices 2 , inl tt) a i))
    ∙ cong {B = λ _ → Path (RoseProduct.Wedge 1) (inr north) (inl north)}
        (λ (r : Path (Susp (RoseProduct.Vertices 1)) north north) →
          (λ i → inr (toSusp (Bool , true) b i))
          ∙∙ sym (push tt) ∙∙ (λ i → inl (r i)))
        (cong-∙ (suspFun (vertexSelection j))
          (merid a) (sym (merid (inl tt))))

  natural : (j : Fin 2) (x : join (RoseProduct.Vertices 2) Bool)
    → Path (RoseProduct.Wedge 1)
        (wedgeSelection j (RoseProduct.W 2 x))
        (RoseProduct.W 1 (joinSelection j x))
  natural j (Join.inl a) = refl
  natural j (Join.inr b) = refl
  natural j (Join.push a b i) k = natural-push j a b k i

lower : Fin 2 → SphereBouquet 1 (Fin 3) → SphereBouquet 1 (Fin 2)
lower j = fst (RoseProduct.target-chart 1) ∘ wedgeSelection j
  ∘ invEq (RoseProduct.target-chart 2)

attachingSelection : Fin 2 → RoseProduct.Rose 2 → RoseProduct.Rose 1
attachingSelection j = invEq (RoseProduct.source-chart 1) ∘ joinSelection j
  ∘ fst (RoseProduct.source-chart 2)

abstract
  lower-point : (j : Fin 2)
    → Path (SphereBouquet 1 (Fin 2)) (lower j (inl tt)) (inl tt)
  lower-point j = refl

  attaching-square : (j : Fin 2) (x : RoseProduct.Rose 2)
    → Path (SphereBouquet 1 (Fin 2))
        (lower j (RoseProduct.attaching 2 x))
        (RoseProduct.attaching 1 (attachingSelection j x))
  attaching-square j x =
    cong (fst (RoseProduct.target-chart 1) ∘ wedgeSelection j)
      (retEq (RoseProduct.target-chart 2)
        (RoseProduct.W 2 (fst (RoseProduct.source-chart 2) x)))
    ∙ cong (fst (RoseProduct.target-chart 1))
        (natural j (fst (RoseProduct.source-chart 2) x))
    ∙ sym (cong (fst (RoseProduct.target-chart 1) ∘ RoseProduct.W 1)
        (secEq (RoseProduct.source-chart 1)
          (joinSelection j (fst (RoseProduct.source-chart 2) x))))

-- Computation on the attaching source.
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Susp using
  (south ; Susp≃joinBool ; S¹IsoSuspBool ; suspFunComp ; suspFunConst)
open import Cubical.HITs.Wedge using (Bouquet→SuspBouquet)

private
  abstract
    joinSelection-susp-merid : (j : Fin 2) (a : RoseProduct.Vertices 2)
      → Path (Path (join (RoseProduct.Vertices 1) Bool)
          (Join.inr true) (Join.inr false))
          (cong {A = join (RoseProduct.Vertices 2) Bool}
            {B = λ _ → join (RoseProduct.Vertices 1) Bool}
            {x = Join.inr true} {y = Join.inr false}
            (joinSelection j)
            (sym (Join.push a true) ∙ Join.push a false))
          (sym (Join.push (vertexSelection j a) true)
            ∙ Join.push (vertexSelection j a) false)
    joinSelection-susp-merid j a =
      cong-∙ {A = join (RoseProduct.Vertices 2) Bool}
        {x = Join.inr true} {y = Join.inl a} {z = Join.inr false}
        {B = join (RoseProduct.Vertices 1) Bool}
        (joinSelection j) (sym (Join.push a true)) (Join.push a false)

abstract
  joinSelection-susp-natural : (j : Fin 2) (x : Susp (RoseProduct.Vertices 2))
    → Path (join (RoseProduct.Vertices 1) Bool)
        (joinSelection j (fst (Susp≃joinBool {A = RoseProduct.Vertices 2}) x))
        (fst (Susp≃joinBool {A = RoseProduct.Vertices 1})
          (suspFun (vertexSelection j) x))
  joinSelection-susp-natural j north = refl
  joinSelection-susp-natural j south = refl
  joinSelection-susp-natural j (merid a i) k = joinSelection-susp-merid j a k i

  attachingSelection-susp : (j : Fin 2) (x : RoseProduct.Rose 2)
    → Path (RoseProduct.Rose 1)
        (attachingSelection j x)
        (fst (RoseProduct.suspension-chart 1)
          (suspFun (vertexSelection j)
            (invEq (RoseProduct.suspension-chart 2) x)))
  attachingSelection-susp j x =
    cong {A = join (RoseProduct.Vertices 1) Bool}
      {B = λ _ → RoseProduct.Rose 1}
      (fst (RoseProduct.suspension-chart 1)
        ∘ invEq (Susp≃joinBool {A = RoseProduct.Vertices 1}))
      (joinSelection-susp-natural j (invEq (RoseProduct.suspension-chart 2) x))
    ∙ cong {A = Susp (RoseProduct.Vertices 1)}
        {B = λ _ → RoseProduct.Rose 1}
        (fst (RoseProduct.suspension-chart 1))
        (retEq (Susp≃joinBool {A = RoseProduct.Vertices 1})
          (suspFun (vertexSelection j)
            (invEq (RoseProduct.suspension-chart 2) x)))

abstract
  inverse-petal-chart : (n : ℕ) (k : Fin n) (z : Susp Bool)
    → Path (Susp (RoseProduct.Vertices n))
        (Bouquet→SuspBouquet (Fin n) (λ _ → Bool , true) (inr (k , z)))
        (suspFun (λ b → inr (k , b)) z)
  inverse-petal-chart n k north = refl
  inverse-petal-chart n k south = refl
  inverse-petal-chart n k (merid b i) = refl

  suspension-chart-inverse-cell : (n : ℕ) (k : Fin n) (s : S¹)
    → Path (Susp (RoseProduct.Vertices n))
        (invEq (RoseProduct.suspension-chart n) (inr (k , s)))
        (suspFun (λ b → inr (k , b)) (Iso.fun S¹IsoSuspBool s))
  suspension-chart-inverse-cell n k s =
    inverse-petal-chart n k (Iso.fun S¹IsoSuspBool s)

selectedRose : Bool → S¹ → RoseProduct.Rose 1
selectedRose true s = inr (fzero , s)
selectedRose false s = inl tt

private
  abstract
    branch : (b : Bool) (s : S¹)
      → Path (RoseProduct.Rose 1)
          (fst (RoseProduct.suspension-chart 1)
            (suspFun (selectedVertex b) (Iso.fun S¹IsoSuspBool s)))
          (selectedRose b s)
    branch true s =
      cong {A = Susp (RoseProduct.Vertices 1)}
        {B = λ _ → RoseProduct.Rose 1}
        (fst (RoseProduct.suspension-chart 1))
        (sym (suspension-chart-inverse-cell 1 fzero s))
      ∙ secEq (RoseProduct.suspension-chart 1) (inr (fzero , s))
    branch false s =
      cong {A = Susp (RoseProduct.Vertices 1)}
        {B = λ _ → RoseProduct.Rose 1}
        (fst (RoseProduct.suspension-chart 1))
        (funExt⁻ (suspFunConst {B = RoseProduct.Vertices 1} {A = Bool} (inl tt))
          (Iso.fun S¹IsoSuspBool s))

abstract
  attachingSelection-cell : (j k : Fin 2) (s : S¹)
    → Path (RoseProduct.Rose 1)
        (attachingSelection j (inr (k , s)))
        (selectedRose (selected j k) s)
  attachingSelection-cell j k s =
    attachingSelection-susp j (inr (k , s))
    ∙ cong {A = Susp (RoseProduct.Vertices 1)}
        {B = λ _ → RoseProduct.Rose 1}
        (fst (RoseProduct.suspension-chart 1))
        (cong {A = Susp (RoseProduct.Vertices 2)}
          {B = λ _ → Susp (RoseProduct.Vertices 1)}
          (suspFun (vertexSelection j))
          (suspension-chart-inverse-cell 2 k s)
        ∙ funExt⁻ (sym (suspFunComp (vertexSelection j)
            (λ (b : Bool) → inr (k , b))))
            (Iso.fun S¹IsoSuspBool s))
    ∙ branch (selected j k) s

-- Direct attachment maps and their sparse bouquet quotients.
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Pushout using (Pushout)
open import Cubical.HITs.Sn using (S₊ ; σSn)
open import Cubical.HITs.SphereBouquet using (Pushout→Bouquet)
  renaming (BouquetIso-gen to BouquetIso-gen2)

sphereBranch : Bool → S₊ 2 → SphereBouquet 2 (Fin 1)
sphereBranch true s = inr (fzero , s)
sphereBranch false s = inl tt

branchPush : (b : Bool)
  → Path (SphereBouquet 2 (Fin 1)) (inl tt) (sphereBranch b north)
branchPush true = push fzero
branchPush false = refl

pointedSparse : Fin 2 → SphereBouquet 2 (Fin 2) → SphereBouquet 2 (Fin 1)
pointedSparse j (inl tt) = inl tt
pointedSparse j (inr (k , s)) = sphereBranch (selected j k) s
pointedSparse j (push k i) = branchPush (selected j k) i

module DirectAttachment (j : Fin 2) {X Y : Type}
  (α : Fin 2 × S¹ → X) (β : Fin 1 × S¹ → Y)
  (L : X → Y) (c : Y) where

  end : Bool → S¹ → Y
  end true s = β (fzero , s)
  end false s = c

  Px : Type
  Px = Pushout α fst

  Py : Type
  Py = Pushout β fst

  center : Bool → Py
  center true = inr fzero
  center false = inl c

  spoke : (b : Bool) (s : S¹)
    → Path Py (inl (end b s)) (center b)
  spoke true s = push (fzero , s)
  spoke false s = refl

  bx : Px → SphereBouquet 2 (Fin 2)
  bx = Pushout→Bouquet 2 2 α (idEquiv Px)

  by : Py → SphereBouquet 2 (Fin 1)
  by = Pushout→Bouquet 2 1 β (idEquiv Py)

  abstract
    -- For a neutral Boolean the two constructor expressions need a path;
    -- each Boolean case is reflexivity.
    center-image : (b : Bool)
      → Path (SphereBouquet 2 (Fin 1)) (by (center b)) (sphereBranch b north)
    center-image true = refl
    center-image false = refl

    spoke-image : (b : Bool) (s : S¹)
      → Square (cong by (spoke b s))
          (branchPush b ∙ (λ i → sphereBranch b (σSn 1 s i)))
          refl (center-image b)
    spoke-image true s = refl
    spoke-image false s = lUnit refl

  module _ (H : (k : Fin 2) (s : S¹)
    → L (α (k , s)) ≡ end (selected j k) s) where

    F : Px → Py
    F (inl x) = inl (L x)
    F (inr k) = center (selected j k)
    F (push (k , s) i) =
      (cong inl (H k s) ∙ spoke (selected j k) s) i

    abstract
      P-push : (k : Fin 2) (s : S¹)
        → Square
            (cong by (cong inl (H k s) ∙ spoke (selected j k) s))
            (cong (pointedSparse j) (cong bx (push (k , s))))
            refl (center-image (selected j k))
      P-push k s =
        (cong-∙ by (cong inl (H k s)) (spoke (selected j k) s)
          ∙ sym (lUnit (cong by (spoke (selected j k) s))))
        ◁ spoke-image (selected j k) s
        ▷ sym (cong-∙ (pointedSparse j)
            (push k) (λ i → inr (k , σSn 1 s i)))

      P-square : (u : Px)
        → Path (SphereBouquet 2 (Fin 1))
            (by (F u)) (pointedSparse j (bx u))
      P-square (inl x) = refl
      P-square (inr k) = center-image (selected j k)
      P-square (push (k , s) i) r = P-push k s r i

    module ActualStage {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py) where
      stageTop : Zx → Zy
      stageTop = invEq eY ∘ F ∘ fst eX

      incX : X → Zx
      incX = invEq eX ∘ inl

      incY : Y → Zy
      incY = invEq eY ∘ inl

      comm : (x : X) → incY (L x) ≡ stageTop (incX x)
      comm x = sym (cong (invEq eY ∘ F) (secEq eX (inl x)))

      Q : cofib incX → cofib incY
      Q (inl tt) = inl tt
      Q (inr z) = inr (stageTop z)
      Q (push x i) =
        (push (L x)
          ∙ cong {A = Zy} {B = λ _ → cofib incY}
              {x = incY (L x)} {y = stageTop (incX x)}
              inr (comm x)) i

      CTBx : cofib incX → SphereBouquet 2 (Fin 2)
      CTBx = Iso.fun (BouquetIso-gen2 2 2 α eX)

      CTBy : cofib incY → SphereBouquet 2 (Fin 1)
      CTBy = Iso.fun (BouquetIso-gen2 2 1 β eY)

    module IdentityStage = ActualStage (idEquiv Px) (idEquiv Py)

    BouquetSquare : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py) → Type
    BouquetSquare eX eY =
      ActualStage.CTBy eX eY ∘ ActualStage.Q eX eY
        ∘ Iso.inv (BouquetIso-gen2 2 2 α eX)
      ≡ pointedSparse j

    abstract
      identity-outer-push : (x : X)
        → Path (Path (SphereBouquet 2 (Fin 1)) (inl tt) (inl tt))
            (cong IdentityStage.CTBy (cong IdentityStage.Q (push x)))
            refl
      identity-outer-push x =
        cong-∙ IdentityStage.CTBy (push (L x)) refl ∙ sym (lUnit refl)

      identity-quotient-point : (z : cofib IdentityStage.incX)
        → Path (SphereBouquet 2 (Fin 1))
            (IdentityStage.CTBy (IdentityStage.Q z))
            (pointedSparse j (IdentityStage.CTBx z))
      identity-quotient-point (inl tt) = refl
      identity-quotient-point (inr u) = P-square u
      identity-quotient-point (push x i) r = identity-outer-push x r i

      identity-quotient-square :
        IdentityStage.CTBy ∘ IdentityStage.Q
          ≡ pointedSparse j ∘ IdentityStage.CTBx
      identity-quotient-square = funExt identity-quotient-point

      identity-bouquet-square : BouquetSquare (idEquiv Px) (idEquiv Py)
      identity-bouquet-square =
        cong (λ f → f ∘ Iso.inv (BouquetIso-gen2 2 2 α (idEquiv Px)))
          identity-quotient-square
        ∙ funExt (λ s → cong (pointedSparse j)
            (Iso.sec (BouquetIso-gen2 2 2 α (idEquiv Px)) s))

      bouquet-square : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py)
        → BouquetSquare eX eY
      bouquet-square {Zx = Zx} {Zy = Zy} eX eY =
        EquivJ
          (λ Zx eX → (Zy : Type) → (eY : Zy ≃ Py) → BouquetSquare eX eY)
          (λ Zy eY → EquivJ
            (λ Zy eY → BouquetSquare (idEquiv Px) eY)
            identity-bouquet-square eY)
          eX Zy eY

-- The actual cell attachments of the RoseProduct skeleta.
cell-attaching : (n : ℕ) → Fin n × S¹ → SphereBouquet 1 (Fin (suc n))
cell-attaching n = CWskel-fields.α (RoseProduct.skeleton n) 2

cell-attachment : (n : ℕ)
  → cofib (RoseProduct.attaching n) ≃ Pushout (cell-attaching n) fst
cell-attachment n = CWskel-fields.e (RoseProduct.skeleton n) 2

abstract
  cell-attaching-beta : (n : ℕ) (k : Fin n) (s : S¹)
    → Path (SphereBouquet 1 (Fin (suc n)))
        (cell-attaching n (k , s)) (RoseProduct.attaching n (inr (k , s)))
  cell-attaching-beta n k s =
    cong {A = S¹} {B = λ _ → SphereBouquet 1 (Fin (suc n))}
      (λ t → RoseProduct.attaching n (inr (k , t))) (transportRefl s)

module SparseStage (j : Fin 2) where
  module D = DirectAttachment j (cell-attaching 2) (cell-attaching 1)
    (lower j) (inl tt)

  abstract
    branch-end : (b : Bool) (s : S¹)
      → Path (SphereBouquet 1 (Fin 2))
          (RoseProduct.attaching 1 (selectedRose b s)) (D.end b s)
    branch-end true s = sym (cell-attaching-beta 1 fzero s)
    branch-end false s = RoseProduct.attaching-point 1

    square : (k : Fin 2) (s : S¹)
      → Path (SphereBouquet 1 (Fin 2))
          (lower j (cell-attaching 2 (k , s))) (D.end (selected j k) s)
    square k s =
      cong {A = SphereBouquet 1 (Fin 3)}
        {B = λ _ → SphereBouquet 1 (Fin 2)}
        (lower j) (cell-attaching-beta 2 k s)
      ∙ attaching-square j (inr (k , s))
      ∙ cong {A = RoseProduct.Rose 1} {B = λ _ → SphereBouquet 1 (Fin 2)}
          (RoseProduct.attaching 1) (attachingSelection-cell j k s)
      ∙ branch-end (selected j k) s

  module Stage = D.ActualStage square (cell-attachment 2) (cell-attachment 1)

  onCells : D.Px → D.Py
  onCells = D.F square

sparseTop : Fin 2 → cofib (RoseProduct.attaching 2) → cofib (RoseProduct.attaching 1)
sparseTop j = SparseStage.Stage.stageTop j

sparseCellular : Fin 2 → cellMap (RoseProduct.skeleton 2) (RoseProduct.skeleton 1)
SequenceMap.map (sparseCellular j) zero ()
SequenceMap.map (sparseCellular j) (suc zero) _ = tt
SequenceMap.map (sparseCellular j) (suc (suc zero)) = lower j
SequenceMap.map (sparseCellular j) (suc (suc (suc n))) = sparseTop j
SequenceMap.comm (sparseCellular j) zero ()
SequenceMap.comm (sparseCellular j) (suc zero) tt = sym (lower-point j)
SequenceMap.comm (sparseCellular j) (suc (suc zero)) x = SparseStage.Stage.comm j x
SequenceMap.comm (sparseCellular j) (suc (suc (suc n))) x = refl

actualQuotient : (j : Fin 2)
  → cofibCW 2 (RoseProduct.skeleton 2) → cofibCW 2 (RoseProduct.skeleton 1)
actualQuotient j =
  prefunctoriality.fn+1/fn 3 (restrictCell (sparseCellular j) 3) (2 , <ᵗsuc {m = 2})

abstract
  actualQuotient-Q : (j : Fin 2) → actualQuotient j ≡ SparseStage.Stage.Q j
  actualQuotient-Q j = funExt
    λ { (inl tt) → refl ; (inr z) → refl ; (push x i) → refl }

  sparseCellular-quotient : (j : Fin 2)
    → ProjectH2.cellular-square-quotient (sparseCellular j) ≡ pointedSparse j
  sparseCellular-quotient j =
    cong (λ (q : cofibCW 2 (RoseProduct.skeleton 2)
                  → cofibCW 2 (RoseProduct.skeleton 1)) →
      SparseStage.Stage.CTBy j ∘ q
        ∘ Iso.inv (BouquetIso-gen2 2 2 (cell-attaching 2) (cell-attachment 2)))
      (actualQuotient-Q j)
    ∙ SparseStage.D.bouquet-square j (SparseStage.square j)
        (cell-attachment 2) (cell-attachment 1)

-- Direct scalar degrees of the actual cellular quotient.
open import Cubical.HITs.Sn.Degree using (degree ; degreeIdfun ; degreeConst)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤFinGenerator)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module GraphProduct ; torus-square-coordinate)

abstract
  pointedSparse-degree : (j k : Fin 2)
    → degree 2 (λ s → pickPetal fzero (pointedSparse j (inr (k , s))))
      ≡ ℤFinGenerator k j
  pointedSparse-degree (zero , _) (zero , _) = degreeIdfun 2
  pointedSparse-degree (zero , _) (suc zero , _) = degreeConst 2
  pointedSparse-degree (suc zero , _) (zero , _) = degreeConst 2
  pointedSparse-degree (suc zero , _) (suc zero , _) = degreeIdfun 2
  pointedSparse-degree (suc (suc n) , ()) _
  pointedSparse-degree _ (suc (suc n) , ())

  sparseCellular-degree : (j k : Fin 2)
    → degree 2 (λ s → pickPetal fzero
        (ProjectH2.cellular-square-quotient (sparseCellular j) (inr (k , s))))
      ≡ ℤFinGenerator k j
  sparseCellular-degree j k =
    cong (λ (F : SphereBouquet 2 (Fin 2) → SphereBouquet 2 (Fin 1)) →
      degree 2 (λ s → pickPetal fzero (F (inr (k , s)))))
      (sparseCellular-quotient j)
    ∙ pointedSparse-degree j k

  sparseCellular-realise-top : (j : Fin 2) (x : cofib (RoseProduct.attaching 2))
    → realiseCellMap (sparseCellular j)
        (fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 2))) x)
      ≡ fst (snd (hasCWskelSphereBouquet/ (RoseProduct.attaching 1))) (sparseTop j x)
  sparseCellular-realise-top j x = refl

-- Marked realization agreement, constructed in ProjectH2Realization.
SparseMarkedAgreement : Fin 2 → Type
SparseMarkedAgreement j =
  realiseCellMap (sparseCellular j) ∘ fst (snd graph×circle-skeleton)
    ≡ fst (snd torus-skeleton) ∘ ProjectH2.project j

abstract
  project-H₂ : (j : Fin 2) → SparseMarkedAgreement j
    → (z : fst (H̃ᶜʷ graph×circleCW 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = graph×circleCW} {D = torusCW} 2 (ProjectH2.project j)) z)
      ≡ GraphProduct.square-coordinate z j
  project-H₂ j agreement z =
    ProjectH2.project-H₂-from-degrees j (sparseCellular j) agreement
      (sparseCellular-degree j) z

