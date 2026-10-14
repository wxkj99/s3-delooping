{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.LocalizationMaps where

-- Functoriality of RouteB2.L-map and the specified inclusions Maps.ι_m/ι_n.
-- All endpoints are in Type = Type ℓ-zero, as in Local.Base.L.
-- Each uniqueness proof retains its value on η behind the abstract boundary;
-- no independently chosen localization equivalences are compared.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; isEquiv)
open import Cubical.Data.Nat using (ℕ ; _·_)
open import DeloopS3.Local.Base using (F ; L ; η ; local-L)
open import DeloopS3.Local.RouteB2.Common public using (L-map)
open import DeloopS3.Local.Unique using (module Unique)
import DeloopS3.Local.Fracture.Fracture.Maps as Maps
import DeloopS3.Assembly.Final.Localization as Existing

abstract
  L-map-β : (m : ℕ) {A B : Type} (f : A → B) (a : A)
    → L-map m f (η {m} {A} a) ≡ η {m} {B} (f a)
  L-map-β m f a = refl

  η-natural : (m : ℕ) {A B : Type} (f : A → B)
    → L-map m f ∘ η {m} {A} ≡ η {m} {B} ∘ f
  η-natural m f = refl

  η-natural-β : (m : ℕ) {A B : Type} (f : A → B) (a : A)
    → funExt⁻ (η-natural m f) a ≡ refl
  η-natural-β m f a = refl

  L-map-id : (m : ℕ) (A : Type)
    → L-map m (idfun A) ≡ idfun (L m A)
  L-map-id m A = Unique.unique {F = F m} {X = A} {Y = L m A}
    (local-L m A) (L-map m (idfun A)) (idfun (L m A)) (λ _ → refl)

  L-map-id-β : (m : ℕ) (A : Type) (a : A)
    → funExt⁻ (L-map-id m A) (η {m} {A} a) ≡ refl
  L-map-id-β m A a = refl

  L-map-comp : (m : ℕ) {A B C : Type} (f : A → B) (g : B → C)
    → L-map m (g ∘ f) ≡ L-map m g ∘ L-map m f
  L-map-comp m {A} {B} {C} f g =
    Unique.unique {F = F m} {X = A} {Y = L m C}
      (local-L m C) (L-map m (g ∘ f)) (L-map m g ∘ L-map m f)
      (λ _ → refl)

  L-map-comp-β : (m : ℕ) {A B C : Type}
    (f : A → B) (g : B → C) (a : A)
    → funExt⁻ (L-map-comp m f g) (η {m} {A} a) ≡ refl
  L-map-comp-β m f g a = refl

  L-map-homotopy : (m : ℕ) {A B : Type} (f g : A → B)
    (h : (a : A) → f a ≡ g a) → L-map m f ≡ L-map m g
  L-map-homotopy m {A} {B} f g h =
    Unique.unique {F = F m} {X = A} {Y = L m B}
      (local-L m B) (L-map m f) (L-map m g)
      (λ a → cong (η {m} {B}) (h a))

  L-map-homotopy-β : (m : ℕ) {A B : Type} (f g : A → B)
    (h : (a : A) → f a ≡ g a) (a : A)
    → funExt⁻ (L-map-homotopy m f g h) (η {m} {A} a)
      ≡ cong (η {m} {B}) (h a)
  L-map-homotopy-β m f g h a = refl

  -- Reuse the inverse construction proved by Unique.≡onη.
  L-map-isEquiv : (m : ℕ) {A B : Type} (e : A ≃ B)
    → isEquiv (L-map m (equivFun e))
  L-map-isEquiv m {A} {B} e = Existing.L-map-isEquiv m A B e

-- Keep the specified forward function transparent, the isEquiv witness opaque.
L-equiv : (m : ℕ) {A B : Type} → A ≃ B → L m A ≃ L m B
L-equiv m e = L-map m (equivFun e) , L-map-isEquiv m e

abstract
  L-equiv-map : (m : ℕ) {A B : Type} (e : A ≃ B)
    → equivFun (L-equiv m e) ≡ L-map m (equivFun e)
  L-equiv-map m e = refl

  L-equiv-β : (m : ℕ) {A B : Type} (e : A ≃ B) (a : A)
    → equivFun (L-equiv m e) (η {m} {A} a)
      ≡ η {m} {B} (equivFun e a)
  L-equiv-β m e a = refl

  ι_m-natural : (m n : ℕ) {A B : Type} (f : A → B)
    → L-map (m · n) f ∘ Maps.ι_m m n A
      ≡ Maps.ι_m m n B ∘ L-map m f
  ι_m-natural m n {A} {B} f =
    Unique.unique {F = F m} {X = A} {Y = L (m · n) B}
      (Maps.overlap-local-m m n B)
      (L-map (m · n) f ∘ Maps.ι_m m n A)
      (Maps.ι_m m n B ∘ L-map m f) (λ _ → refl)

  ι_m-natural-β : (m n : ℕ) {A B : Type} (f : A → B) (a : A)
    → funExt⁻ (ι_m-natural m n f) (η {m} {A} a) ≡ refl
  ι_m-natural-β m n f a = refl

  ι_n-natural : (m n : ℕ) {A B : Type} (f : A → B)
    → L-map (m · n) f ∘ Maps.ι_n m n A
      ≡ Maps.ι_n m n B ∘ L-map n f
  ι_n-natural m n {A} {B} f =
    Unique.unique {F = F n} {X = A} {Y = L (m · n) B}
      (Maps.overlap-local-n m n B)
      (L-map (m · n) f ∘ Maps.ι_n m n A)
      (Maps.ι_n m n B ∘ L-map n f) (λ _ → refl)

  ι_n-natural-β : (m n : ℕ) {A B : Type} (f : A → B) (a : A)
    → funExt⁻ (ι_n-natural m n f) (η {n} {A} a) ≡ refl
  ι_n-natural-β m n f a = refl

-- The actual mixed-modulus composites, generic in the underlying map.
overlap-map-m : (m n : ℕ) {A B : Type} → (A → B) → L m A → L (m · n) B
overlap-map-m m n {A} f = L-map (m · n) f ∘ Maps.ι_m m n A

overlap-map-n : (m n : ℕ) {A B : Type} → (A → B) → L n A → L (m · n) B
overlap-map-n m n {A} f = L-map (m · n) f ∘ Maps.ι_n m n A

abstract
  overlap-map-m-β : (m n : ℕ) {A B : Type} (f : A → B) (a : A)
    → overlap-map-m m n f (η {m} {A} a) ≡ η {m · n} {B} (f a)
  overlap-map-m-β m n f a = refl

  overlap-map-n-β : (m n : ℕ) {A B : Type} (f : A → B) (a : A)
    → overlap-map-n m n f (η {n} {A} a) ≡ η {m · n} {B} (f a)
  overlap-map-n-β m n f a = refl

-- Specializations are definitionally the 3/10 → 30 inclusions.
ι₃ : (A : Type) → L 3 A → L 30 A
ι₃ = Maps.ι_m 3 10

ι₁₀ : (A : Type) → L 10 A → L 30 A
ι₁₀ = Maps.ι_n 3 10

ι₃-natural : {A B : Type} (f : A → B)
  → L-map 30 f ∘ ι₃ A ≡ ι₃ B ∘ L-map 3 f
ι₃-natural = ι_m-natural 3 10

ι₁₀-natural : {A B : Type} (f : A → B)
  → L-map 30 f ∘ ι₁₀ A ≡ ι₁₀ B ∘ L-map 10 f
ι₁₀-natural = ι_n-natural 3 10

overlap-map₃ : {A B : Type} → (A → B) → L 3 A → L 30 B
overlap-map₃ = overlap-map-m 3 10

overlap-map₁₀ : {A B : Type} → (A → B) → L 10 A → L 30 B
overlap-map₁₀ = overlap-map-n 3 10
