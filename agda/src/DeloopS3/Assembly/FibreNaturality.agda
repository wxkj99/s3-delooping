{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.FibreNaturality where

-- The I-side homotopy comes from the actual pushout square.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed.Base
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.HITs.Pushout.Base

-- These opaque, universe-polymorphic path calculations keep the concrete
-- mixed-descent equivalence proofs out of conversion checking.
module PathAlgebra where
  abstract
    rotate-square : {ℓ : Level} {X : Type ℓ} {a b c d : X}
      (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d)
      → p ∙ s ≡ r ∙ q
      → q ∙ sym s ≡ sym r ∙ p
    rotate-square p q r s H =
      cong (_∙ sym s) (sym (compPathl-cancel (sym r) q))
      ∙ sym (assoc (sym r) (r ∙ q) (sym s))
      ∙ cong (λ z → sym r ∙ (z ∙ sym s)) (sym H)
      ∙ cong (sym r ∙_) (compPathr-cancel (sym s) p)

    fibre-path-over : {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'}
      (f : X → Y) {x y : X} {z : Y}
      (e : x ≡ y) (p : f x ≡ z) (q : f y ≡ z)
      → p ≡ cong f e ∙ q
      → PathP (λ i → f (e i) ≡ z) p q
    fibre-path-over f e p q H = compPathR→PathP
      {p = cong f e} {q = refl} {r = p} {s = q}
      (H ∙ cong (cong f e ∙_) (rUnit q))

    -- Cancel precomposition by the SPECIFIED equivalence, without replacing
    -- either of the functions whose equality is requested.
    cancel-coordinate : {ℓ ℓ' ℓ'' : Level}
      {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      (e : X ≃ Y) (d : X ≃ Z) (v : Y → Z)
      → v ∘ equivFun e ≡ equivFun d
      → invEq d ∘ v ≡ invEq e
    cancel-coordinate e d v H = funExt λ y →
      cong (invEq d ∘ v) (sym (secEq e y))
      ∙ cong (invEq d) (funExt⁻ H (invEq e y))
      ∙ retEq d (invEq e y)

  -- Retain the first coordinate definitionally: the pointing below must have
  -- first coordinate sym (push r₀), not an independently chosen path.
  fibre-path : {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'}
    (f : X → Y) {x y : X} {z : Y}
    (e : x ≡ y) (p : f x ≡ z) (q : f y ≡ z)
    → p ≡ cong f e ∙ q
    → (x , p) ≡ (y , q)
  fibre-path f e p q H i = e i , fibre-path-over f e p q H i

-- StarCube supplies the specified fibre maps and their equivalence proofs.
open import DeloopS3.Assembly.StarCube public

abstract
  -- Congruence-composition computes pointwise, without a new chosen homotopy.
  naturality-O : UO ∘ λG octa ≡ λ*
  naturality-O = refl

  lower-square : (r : R) (s : u r ≡ n₀)
    → cong (kPO ∘ nG octa) s ∙ push n₀
      ≡ push (u r) ∙ cong (kPI ∘ nG icosa) s
  lower-square r s = Square→compPath (λ i j → push (s i) j)

  lower-square-rotated : (r : R) (s : u r ≡ n₀)
    → cong (kPI ∘ nG icosa) s ∙ bI
      ≡ sym (push (u r)) ∙ cong (kPO ∘ nG octa) s
  lower-square-rotated r s = PathAlgebra.rotate-square
    (cong (kPO ∘ nG octa) s) (cong (kPI ∘ nG icosa) s)
    (push (u r)) (push n₀) (lower-square r s)

-- The STRICT seam is used here, not StarRaw's refl ∙ push ∙ refl seam.
strict-seam : (r : R)
  → cong t* (sym (push r)) ≡ sym (push (u r))
strict-seam r = refl

naturality-I-at : (f : F) → UI (λG icosa f) ≡ λ* f
naturality-I-at (r , s) = PathAlgebra.fibre-path t*
  (sym (push r))
  (cong (kPI ∘ nG icosa) s ∙ bI)
  (cong (kPO ∘ nG octa) s)
  (lower-square-rotated r s)

naturality-I : UI ∘ λG icosa ≡ λ*
naturality-I = funExt naturality-I-at

χG : (c : Case) → fiber (t c) (pG₀ c) ≃ F
χG c = invEquiv (local-fibre c)

χ* : fiber t* p*₀ ≃ F
χ* = invEquiv (λ* , λ*-isEquiv)

abstract
  identity-O : equivFun χ* ∘ UO ∘ λG octa ≡ idfun F
  identity-O = cong (equivFun χ* ∘_) naturality-O
    ∙ funExt (retEq (λ* , λ*-isEquiv))

  identity-I : equivFun χ* ∘ UI ∘ λG icosa ≡ idfun F
  identity-I = cong (equivFun χ* ∘_) naturality-I
    ∙ funExt (retEq (λ* , λ*-isEquiv))

  coordinate-O : equivFun χ* ∘ UO ≡ equivFun (χG octa)
  coordinate-O = PathAlgebra.cancel-coordinate
    (local-fibre octa) (λ* , λ*-isEquiv) UO naturality-O

  coordinate-I : equivFun χ* ∘ UI ≡ equivFun (χG icosa)
  coordinate-I = PathAlgebra.cancel-coordinate
    (local-fibre icosa) (λ* , λ*-isEquiv) UI naturality-I

-- The local and common fibres are pointed in the common F coordinate.
FG∙ : (c : Case) → Pointed ℓ-zero
FG∙ c = fiber (t c) (pG₀ c) , λG c f₀

F*∙ : Pointed ℓ-zero
F*∙ = fiber t* p*₀ , λ* f₀

λG∙ : (c : Case) → (F , f₀) ≃∙ FG∙ c
λG∙ c = local-fibre c , refl

λ*∙ : (F , f₀) ≃∙ F*∙
λ*∙ = (λ* , λ*-isEquiv) , refl

UO-pointing : UO (λG octa f₀) ≡ λ* f₀
UO-pointing = funExt⁻ naturality-O f₀

-- By DEFINITION this is the value of the I-side naturality homotopy.
UI-pointing : UI (λG icosa f₀) ≡ λ* f₀
UI-pointing = funExt⁻ naturality-I f₀

UI-pointing-first : cong fst UI-pointing ≡ aI
UI-pointing-first = refl

UO∙ : FG∙ octa ≃∙ F*∙
UO∙ = (UO , UO-isEquiv) , UO-pointing

UI∙ : FG∙ icosa ≃∙ F*∙
UI∙ = (UI , UI-isEquiv) , UI-pointing

-- Case-indexed interface for localization and the single sphere coordinate.
UG : (c : Case) → fiber (t c) (pG₀ c) → fiber t* p*₀
UG octa = UO
UG icosa = UI

UG-isEquiv : (c : Case) → isEquiv (UG c)
UG-isEquiv octa = UO-isEquiv
UG-isEquiv icosa = UI-isEquiv

naturality-G : (c : Case) → UG c ∘ λG c ≡ λ*
naturality-G octa = naturality-O
naturality-G icosa = naturality-I

coordinate-G : (c : Case) → equivFun χ* ∘ UG c ≡ equivFun (χG c)
coordinate-G octa = coordinate-O
coordinate-G icosa = coordinate-I
