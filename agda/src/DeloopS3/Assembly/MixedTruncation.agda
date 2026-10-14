{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.MixedTruncation where

-- Change only the lower source of the τ₂ cartesian square.
-- The homotopy is exactly cong (τ₂-map f) (retEq e (η₂ x)).
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma
open import DeloopS3.Sphere.TruncationCartesian
open import DeloopS3.Assembly.TruncationLevel public
  using (Case; BA; BC; κ; κ-η; κA; κA-isEquiv)
import DeloopS3.Assembly.ActualSpans as Actual

module MixedLeft {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
  (f : X → Y) (κ-equiv : isEquiv (κ {X = X})) where

  e : τ₂ X ≃ τ₁ X
  e = κ , κ-equiv

  fbar : τ₁ X → τ₂ Y
  fbar = τ₂-map f ∘ invEq e

  H : (x : X) → fbar (η₁ x) ≡ η₂ (f x)
  H x = cong (τ₂-map f) (retEq e (η₂ x))

  -- Forward function: (y , z , s) ↦ (y , invEq e z , s).
  -- No transport is needed in the last coordinate: fbar has this definition.
  Θ : PB fbar (η₂ {A = Y}) ≃ PB (τ₂-map f) (η₂ {A = Y})
  Θ = Σ-cong-equiv-snd {A = Y} λ y →
    Σ-cong-equiv-fst {A = τ₁ X} {A' = τ₂ X}
      {B = λ z → τ₂-map f z ≡ η₂ y} (invEquiv e)

  abstract
    -- The terminal segment of retEq contracts H to the canonical refl.
    -- Both the middle coordinate and the path coordinate are retained.
    comparison-path :
      equivFun Θ ∘ squareComparison f fbar η₁ η₂ H
        ≡ squareComparison f (τ₂-map f) η₂ η₂ (trunc₂-naturality f)
    comparison-path = funExt λ x i →
      f x , retEq e (η₂ x) i ,
        (λ j → τ₂-map f (retEq e (η₂ x) (i ∨ j)))

    cartesian : CartSquare f (τ₂-map f) η₂ η₂ (trunc₂-naturality f)
      → CartSquare f fbar η₁ η₂ H
    CartSquare.comparison-isEquiv (cartesian cart₂) =
      isEquiv[equivFunA≃B∘f]→isEquiv[f]
        (squareComparison f fbar η₁ η₂ H) Θ
        (subst isEquiv (sym comparison-path)
          (CartSquare.comparison-isEquiv cart₂))

-- Public generic adapter; it uses the supplied cartesian square, rather than
-- reproving cartesianness from a fresh description of its fibres.
abstract
  mixed-left-cartesian : ∀ {ℓX ℓY} {X : Type ℓX} {Y : Type ℓY}
    (f : X → Y) (κ-equiv : isEquiv (κ {X = X}))
    → CartSquare f (τ₂-map f) η₂ η₂ (trunc₂-naturality f)
    → CartSquare f (MixedLeft.fbar f κ-equiv) η₁ η₂ (MixedLeft.H f κ-equiv)
  mixed-left-cartesian = MixedLeft.cartesian

u : Actual.R → Actual.N
u = η₂

qbar : (c : Case) → BA c → Actual.N
qbar c = τ₂-map (Actual.q c) ∘ invEq (κA c)

pbar : (c : Case) → BA c → BC c
pbar c = τ₁-map (Actual.p c)

Hq : (c : Case) (a : Actual.A c) → qbar c (η₁ a) ≡ u (Actual.q c a)
Hq c a = cong (τ₂-map (Actual.q c)) (retEq (κA c) (η₂ a))

Hp : (c : Case) (a : Actual.A c) → pbar c (η₁ a) ≡ η₁ (Actual.p c a)
Hp c a = refl

Θ : (c : Case) → PB (qbar c) u ≃ PB (τ₂-map (Actual.q c)) u
Θ c = MixedLeft.Θ (Actual.q c) (κA-isEquiv c)

abstract
  left-cartesian : (c : Case)
    → CartSquare (Actual.q c) (qbar c) η₁ u (Hq c)
  left-cartesian c = mixed-left-cartesian (Actual.q c) (κA-isEquiv c)
    (Actual.left₂-cartesian c)

  -- The Done.B-cartesian square, at τ₁.
  -- No κC, degree, or π₂ transfer across the covering is required.
  right-cartesian : (c : Case)
    → CartSquare (Actual.p c) (pbar c) η₁ η₁ (Hp c)
  right-cartesian = Actual.right₁-cartesian
