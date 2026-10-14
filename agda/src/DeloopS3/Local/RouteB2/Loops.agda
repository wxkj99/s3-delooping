{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Loops where

-- Localization of loops by the constant-map specialization of fibre localization.
open import DeloopS3.Local.RouteB2.Common
open import DeloopS3.Local.RouteB2.Finite
open import DeloopS3.Local.RouteB2.Fibers
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.Telescope using (pow∙ ; module LocalizationUnit)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
import Cubical.HITs.Localization.Properties as Loc

path-comparison : (m : ℕ) {X : Type} (x y : X)
  → L m (x ≡ y) → (η {m} x ≡ η y)
path-comparison m {X} x y = Loc.rec
  (local-path (local-L m X) (η x) (η y)) (cong η)

path-comparison-β : (m : ℕ) {X : Type} (x y : X) (p : x ≡ y)
  → path-comparison m x y (η p) ≡ cong η p
path-comparison-β m x y p = refl

L∙ : (m : ℕ) → Pointed ℓ-zero → Pointed ℓ-zero
L∙ m X = L m (typ X) , η (pt X)

η∙ : (m : ℕ) (X : Pointed ℓ-zero) → X →∙ L∙ m X
η∙ m X = η , refl

loop-comparison : (m : ℕ) (X : Pointed ℓ-zero)
  → L m (typ (Ω X)) → typ (Ω (L∙ m X))
loop-comparison m X = path-comparison m (pt X) (pt X)

localize-loops-β : (m : ℕ) (X : Pointed ℓ-zero)
  → loop-comparison m X ∘ η ≡ cong (η {m} {typ X})
localize-loops-β m X = refl

unit-loop-normalize : (m : ℕ) (X : Pointed ℓ-zero) (p : typ (Ω X))
  → fst (Ω→ (η∙ m X)) p ≡ cong η p
unit-loop-normalize m X p = sym (rUnit (cong η p))

-- Keep cancellation generic: elaboration never needs to normalize the
-- large proof of the fibre universal property to discover its endpoints.
local-equivalence-whisker : {m : ℕ} {A B C D : Type}
  (a : A ≃ B) (u : B → C) (c : C ≃ D) (v : A → D)
  → LocalEquiv m u
  → ((x : A) → equivFun c (u (equivFun a x)) ≡ v x)
  → LocalEquiv m v
local-equivalence-whisker a u c v up β Z lZ = subst isEquiv
  (funExt λ h → funExt λ x → cong h (β x))
  (snd (compEquiv (preCompEquiv c)
    (compEquiv ((λ h → h ∘ u) , up Z lZ) (preCompEquiv a))))

-- The fibre theorem is a parameter of this generic path comparison;
-- RouteB2.agda discharges it with Preservation.fiber-unit-local-equivalence.
module Loops
  (fiber-UP : (m : ℕ) {E B : Type} (f : E → B) (b : B)
    → SC B → LocalEquiv m (fiber-unit m f b))
  where

  module PathProof (m : ℕ) {X : Type} (sc : SC X) (x y : X) where
    f : Unit → X
    f _ = x

    source : (x ≡ y) ≃ fiber f y
    source = isoToEquiv (iso (λ p → tt , p) snd (λ { (tt , p) → refl }) (λ _ → refl))

    constant-square : (z : L m Unit) → L-map m f z ≡ η x
    constant-square = Unique.≡onη (local-L m X) (L-map m f) (λ _ → η x) (λ _ → refl)

    contract : isContr (L m Unit)
    contract = η tt , Unique.≡onη (local-L m Unit)
      (λ _ → η tt) (λ z → z) (λ { tt → refl })

    constant-product : (Σ[ z ∈ L m Unit ] (η {m} x ≡ η y)) ≃ (η {m} x ≡ η y)
    constant-product = isoToEquiv (iso snd (λ p → η tt , p)
      (λ _ → refl) (λ { (z , p) i → snd contract z i , p }))

    target : fiber (L-map m f) (η y) ≃ (η {m} x ≡ η y)
    target = compEquiv
      (Σ-cong-equiv-snd (λ z → compPathlEquiv (sym (constant-square z))))
      constant-product

    target-β : (p : x ≡ y)
      → equivFun target (fiber-unit m f y (equivFun source p)) ≡ cong η p
    target-β p = sym (lUnit (cong η p))

    unit-path-UP : LocalEquiv m (cong {x = x} {y = y} (η {m} {X}))
    unit-path-UP = local-equivalence-whisker {m = m}
      {A = x ≡ y} {B = fiber f y} {C = fiber (L-map m f) (η y)}
      {D = η {m} x ≡ η y} source (fiber-unit m f y) target
      (cong {x = x} {y = y} (η {m} {X}))
      (fiber-UP m {E = Unit} {B = X} f y sc) target-β

  -- Proof witnesses are opaque; the comparison maps and unit laws stay transparent.
  abstract
    unit-path-local-equivalence : (m : ℕ) {X : Type}
      → SC X → (x y : X) → LocalEquiv m (cong {x = x} {y = y} (η {m} {X}))
    unit-path-local-equivalence m {X} sc x y = PathProof.unit-path-UP m {X} sc x y

    path-comparison-isEquiv : (m : ℕ) {X : Type}
      → SC X → (x y : X) → isEquiv (path-comparison m x y)
    path-comparison-isEquiv m {X} sc x y = snd
      (LocalizationUnit.equivalence {F = F m} {X = x ≡ y} {Y = η {m} x ≡ η y}
        (cong {x = x} {y = y} (η {m} {X}))
        (local-path (local-L m X) (η x) (η y)) (unit-path-local-equivalence m sc x y))

  -- Specializing both endpoints to the basepoint gives the loop comparison;
  -- localize-loops-β and unit-loop-normalize retain its pointed unit.
