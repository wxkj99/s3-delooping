{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Sphere.TruncationCartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration using (fiberEquiv; totalEquiv)
open import Cubical.HITs.Truncation as T

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Type ℓA
    B : Type ℓB
    C : Type ℓC
    D : Type ℓD

-- The ordering keeps the bottom-left coordinate first.
PB : (C → D) → (B → D) → Type _
PB {B = B} g v = Σ[ b ∈ B ] fiber g (v b)

squareComparison : (f : A → B) (g : C → D) (u : A → C) (v : B → D)
  → ((a : A) → g (u a) ≡ v (f a)) → A → PB g v
squareComparison f g u v comm a = f a , u a , comm a

record CartSquare {ℓA ℓB ℓC ℓD : Level}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
  (f : A → B) (g : C → D) (u : A → C) (v : B → D)
  (comm : (a : A) → g (u a) ≡ v (f a)) : Type (ℓ-max (ℓ-max ℓA ℓB) (ℓ-max ℓC ℓD)) where
  field
    comparison-isEquiv : isEquiv (squareComparison f g u v comm)

  comparisonEquiv : A ≃ PB g v
  comparisonEquiv = squareComparison f g u v comm , comparison-isEquiv

-- The family of n-types extends over the (n+1)-truncation
-- because its univalent universe has h-level n+1. Its total space is the
-- reflection of A: the following explicit inverse is the truncation
-- elimination form of the connected-map argument in the paper.
module TruncationSquare {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
  (n : ℕ) (f : X → Y) (hf : (y : Y) → isOfHLevel n (fiber f y)) where

  Family : hLevelTrunc (suc n) Y → TypeOfHLevel (ℓ-max ℓX ℓY) n
  Family = T.rec (isOfHLevelTypeOfHLevel n) (λ y → fiber f y , hf y)

  F : hLevelTrunc (suc n) Y → Type (ℓ-max ℓX ℓY)
  F y = fst (Family y)

  Total : Type (ℓ-max ℓX ℓY)
  Total = Σ (hLevelTrunc (suc n) Y) F

  totalLevel : isOfHLevel (suc n) Total
  totalLevel = isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n))
    (λ y → isOfHLevelSuc n (snd (Family y)))

  intoTotal : X → Total
  intoTotal x = ∣ f x ∣ₕ , x , refl

  reflect : hLevelTrunc (suc n) X → Total
  reflect = T.rec totalLevel intoTotal

  back : Total → hLevelTrunc (suc n) X
  back (y , z) = T.elim {B = λ y → F y → hLevelTrunc (suc n) X}
    (λ y → isOfHLevelΠ (suc n) (λ _ → isOfHLevelTrunc (suc n)))
    (λ y z → ∣ fst z ∣ₕ) y z

  reflect-back : (t : Total) → reflect (back t) ≡ t
  reflect-back (y , z) = T.elim
    {B = λ y → (z : F y) → reflect (back (y , z)) ≡ (y , z)}
    (λ y → isOfHLevelΠ (suc n)
      (λ z → isOfHLevelPath (suc n) totalLevel _ _))
    (λ y → λ { (x , p) i → ∣ p i ∣ₕ , x , (λ j → p (i ∧ j)) }) y z

  back-reflect : (x : hLevelTrunc (suc n) X) → back (reflect x) ≡ x
  back-reflect = T.elim
    (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
    (λ _ → refl)

  reflectionIso : Iso (hLevelTrunc (suc n) X) Total
  reflectionIso = iso reflect back reflect-back back-reflect

  projection : (x : hLevelTrunc (suc n) X) → fst (reflect x) ≡ T.map f x
  projection = T.elim
    (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
    (λ _ → refl)

  private
    -- First use the total-space projection, whose square commutes strictly.
    pullback≃Fibers : PB (fst ∘ reflect) ∣_∣ₕ ≃ Σ Y (fiber f)
    pullback≃Fibers = Σ-cong-equiv-snd λ y → compEquiv
      (Σ-cong-equiv-fst {B = λ t → fst t ≡ ∣ y ∣ₕ}
        (isoToEquiv reflectionIso))
      (fiberEquiv F ∣ y ∣ₕ)

    comparison' : X → PB (fst ∘ reflect) ∣_∣ₕ
    comparison' = squareComparison f (fst ∘ reflect) ∣_∣ₕ ∣_∣ₕ (λ _ → refl)

    comparison'-total : equivFun pullback≃Fibers ∘ comparison'
                       ≡ equivFun (totalEquiv f)
    comparison'-total = funExt λ x →
      ΣPathP (refl , transportRefl (x , refl))

    cartesian' : CartSquare f (fst ∘ reflect) ∣_∣ₕ ∣_∣ₕ (λ _ → refl)
    CartSquare.comparison-isEquiv cartesian' =
      isEquiv[equivFunA≃B∘f]→isEquiv[f] comparison' pullback≃Fibers
        (subst isEquiv (sym comparison'-total) (snd (totalEquiv f)))

  -- projection computes to refl on generators, so this transport retains
  -- exactly the canonical naturality path, not an unspecified square.
  cartesian : CartSquare f (T.map {n = suc n} f) ∣_∣ₕ ∣_∣ₕ (λ _ → refl)
  cartesian = transport
    (λ i → CartSquare f (λ x → projection x i) ∣_∣ₕ ∣_∣ₕ (λ _ → refl))
    cartesian'

τ₁ : Type ℓA → Type ℓA
τ₁ = hLevelTrunc 3

τ₂ : Type ℓA → Type ℓA
τ₂ = hLevelTrunc 4

η₁ : A → τ₁ A
η₁ = ∣_∣ₕ

η₂ : A → τ₂ A
η₂ = ∣_∣ₕ

τ₁-map : (A → B) → τ₁ A → τ₁ B
τ₁-map = T.map

τ₂-map : (A → B) → τ₂ A → τ₂ B
τ₂-map = T.map

trunc₂-naturality : (f : A → B) (x : A) → τ₂-map f (η₂ x) ≡ η₂ (f x)
trunc₂-naturality f x = refl

trunc₁-naturality : (f : A → B) (x : A) → τ₁-map f (η₁ x) ≡ η₁ (f x)
trunc₁-naturality f x = refl

trunc₂-cartesian : (f : A → B)
  → ((y : B) → isGroupoid (fiber f y))
  → CartSquare f (τ₂-map f) η₂ η₂ (trunc₂-naturality f)
trunc₂-cartesian = TruncationSquare.cartesian 3

trunc₁-cover-cartesian : (f : A → B)
  → ((y : B) → isSet (fiber f y))
  → CartSquare f (τ₁-map f) η₁ η₁ (trunc₁-naturality f)
trunc₁-cover-cartesian = TruncationSquare.cartesian 2

-- Rotate a pullback and recover the horizontal fibres. The resulting map
-- is transport in the actual target fibre family along the source path.
private
  swapPullbackIso : (g : C → D) (v : B → D)
    → Iso (PB g v) (Σ C (λ c → fiber v (g c)))
  Iso.fun (swapPullbackIso g v) (b , c , p) = c , b , sym p
  Iso.inv (swapPullbackIso g v) (c , b , p) = b , c , sym p
  Iso.sec (swapPullbackIso g v) _ = refl
  Iso.ret (swapPullbackIso g v) _ = refl

cartesianHorizontalFiber : {f : A → B} {g : C → D} {u : A → C} {v : B → D}
  {comm : (a : A) → g (u a) ≡ v (f a)}
  → CartSquare f g u v comm → (c : C) → fiber u c ≃ fiber v (g c)
cartesianHorizontalFiber {g = g} {v = v} square c = compEquiv
  (Σ-cong-equiv-fst {B = λ t → fst t ≡ c}
    (compEquiv (CartSquare.comparisonEquiv square)
               (isoToEquiv (swapPullbackIso g v))))
  (fiberEquiv (λ c → fiber v (g c)) c)

cartesianHorizontalFiber-map : {f : A → B} {g : C → D} {u : A → C} {v : B → D}
  {comm : (a : A) → g (u a) ≡ v (f a)}
  (square : CartSquare f g u v comm) (c : C) (x : A) (p : u x ≡ c)
  → equivFun (cartesianHorizontalFiber square c) (x , p)
    ≡ subst (λ c → fiber v (g c)) p (f x , sym (comm x))
cartesianHorizontalFiber-map square c x p = refl

trunc₂-unit-fibers : (f : A → B) → ((y : B) → isGroupoid (fiber f y))
  → (z : τ₂ A) → fiber η₂ z ≃ fiber η₂ (τ₂-map f z)
trunc₂-unit-fibers f hf = cartesianHorizontalFiber (trunc₂-cartesian f hf)

trunc₁-cover-unit-fibers : (f : A → B) → ((y : B) → isSet (fiber f y))
  → (z : τ₁ A) → fiber η₁ z ≃ fiber η₁ (τ₁-map f z)
trunc₁-cover-unit-fibers f hf = cartesianHorizontalFiber (trunc₁-cover-cartesian f hf)
