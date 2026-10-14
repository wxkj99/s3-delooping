{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2.Finite where

-- Finite loop-power reflection, with pointing pow-refl / pow∙ from
-- Telescope. No sequential-colimit theorem is used.
open import DeloopS3.Local.RouteB2.Common
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.Telescope using (pow-refl ; pow∙)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Embedding
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.Homotopy.Connected using (isConnectedPath)
import Cubical.HITs.Localization.Properties as Loc
import Cubical.HITs.Truncation as Tr
import Cubical.HITs.PropositionalTruncation as PT

connected-mere-path : {A : Type} → Conn A → (x y : A) → PT.∥ x ≡ y ∥₁
connected-mere-path c x y = Tr.rec PT.squash₁ PT.∣_∣₁
  (fst (isConnectedPath 1 c x y))

pointed-loop→raw : {A B : Pointed ℓ-zero} (g : A →∙ B)
  → isEquiv (fst (Ω→ g)) → isEquiv (cong {x = pt A} {y = pt A} (fst g))
pointed-loop→raw {A} {B} (f , p) =
  J (λ b p → isEquiv (fst (Ω→ {A = A} {B = typ B , b} (f , p)))
      → isEquiv (cong {x = pt A} {y = pt A} f))
    (λ e → subst isEquiv (funExt (λ q → sym (rUnit (cong f q)))) e) p

connected-loop-reflection : {A B : Pointed ℓ-zero}
  → Conn (typ A) → Conn (typ B) → (g : A →∙ B)
  → isEquiv (fst (Ω→ g)) → isEquiv (fst g)
connected-loop-reflection {A} {B} cA cB g e .equiv-proof b = center , prop center
  where
  f = fst g
  based : isEquiv (cong {x = pt A} {y = pt A} f)
  based = pointed-loop→raw g e

  embedding : isEmbedding f
  embedding x y = PT.rec (isPropIsEquiv _)
    (λ p → PT.rec (isPropIsEquiv _)
      (λ q → subst (λ y → isEquiv (cong {x = x} {y = y} f)) q
        (subst (λ x → isEquiv (cong {x = x} {y = pt A} f)) p based))
      (connected-mere-path cA (pt A) y))
    (connected-mere-path cA (pt A) x)

  prop : isProp (fiber f b)
  prop = isEmbedding→hasPropFibers embedding b

  center : fiber f b
  center = PT.rec prop (λ p → pt A , p)
    (connected-mere-path cB (f (pt A)) b)

set-local : (m : ℕ) {A : Type} → isSet A → Local m A
set-local m set = powers→local λ x →
  isEquivFromIsContr (powLoop m) (refl , set x x refl) (refl , set x x refl)

one-type-separated : (m : ℕ) {A : Type}
  → isOfHLevel 3 A → Separated m A
one-type-separated m h x y = set-local m (h x y)

unit-on-local : (m : ℕ) {A : Type} → Local m A → isEquiv (η {m} {A})
unit-on-local m {A} lA = isoToIsEquiv (iso η inverse sec-law (λ _ → refl))
  where
  inverse : L m A → A
  inverse = Loc.rec lA (idfun A)
  sec-law : (t : L m A) → η (inverse t) ≡ t
  sec-law = Unique.≡onη (local-L m A) (η ∘ inverse) (idfun _) (λ _ → refl)

module Connectivity (H : RouteB1-Hypotheses) where
  open Suspended H

  S-preserves-SC : (m : ℕ) {X : Type} → SC X → SC (S m X)
  S-preserves-SC m {X} cX = PT.rec isPropIsContr pointed inhabited
    where
    T = Tr.hLevelTrunc 3 (S m X)
    q : S m X → T
    q = Tr.∣_∣
    tSep : Separated m T
    tSep = one-type-separated m (Tr.isOfHLevelTrunc 3)

    pointed : X → SC (S m X)
    pointed x₀ = q (ηS x₀) , Tr.elim
      (λ t → isOfHLevelPath 3 (Tr.isOfHLevelTrunc 3) _ _)
      (λ t → sym (funExt⁻ constant t))
      where
      k : Tr.hLevelTrunc 3 X → T
      k = Tr.rec (Tr.isOfHLevelTrunc 3) (q ∘ ηS)
      constant : q ≡ (λ _ → q (ηS x₀))
      constant = S-unique tSep q (λ _ → q (ηS x₀))
        (λ x → cong k (isContr→isProp cX Tr.∣ x ∣ Tr.∣ x₀ ∣))

    inhabited : PT.∥ X ∥₁
    inhabited = Tr.rec (isProp→isOfHLevelSuc 2 PT.squash₁) PT.∣_∣₁ (fst cX)

  S-to-L : (m : ℕ) {X : Type} → S m X → L m X
  S-to-L m {X} = S-rec (local-path (local-L m X)) η

  S-to-L-β : (m : ℕ) {X : Type} (x : X) → S-to-L m (ηS x) ≡ η x
  S-to-L-β m x = refl

-- Finite interface, discharged by Derivative.loop-power-derivative
-- in RouteB2.agda.  Keeping the argument explicit separates the finite
-- cubical normalization from the reflection argument.  Its pointing is
-- Telescope.pow-refl, not an arbitrary re-pointing.
module Reflection (H : RouteB1-Hypotheses)
  (loop-power-derivative : (m : ℕ) (X : Pointed ℓ-zero)
    → (q : typ (Ω (Ω X))) → fst (Ω→ (pow∙ m X)) q ≡ powLoop m q)
  where
  open Suspended H
  open Connectivity H public

  connected-local-loop-power : (m : ℕ) (X : Pointed ℓ-zero)
    → Conn (typ (Ω X)) → Local m (typ (Ω X))
    → isEquiv (powLoop {x = pt X} m)
  connected-local-loop-power m X conn local =
    connected-loop-reflection conn conn (pow∙ m X)
      (subst isEquiv (sym (funExt (loop-power-derivative m X)))
        (local→powers local refl))

  SC-separated→local : (m : ℕ) {X : Type} → SC X → Separated m X → Local m X
  SC-separated→local m {X} sc sep = powers→local λ x →
    connected-local-loop-power m (X , x) (isConnectedPath 2 sc x x) (sep x x)

  local-S-SC : (m : ℕ) {X : Type} → SC X → Local m (S m X)
  local-S-SC m {X} sc = SC-separated→local m
    (S-preserves-SC m sc) (separated-S m X)

  S-to-L-isEquiv : (m : ℕ) {X : Type} → SC X → isEquiv (S-to-L m {X})
  S-to-L-isEquiv m {X} sc = isoToIsEquiv (iso (S-to-L m) inverse sec-law ret-law)
    where
    inverse : L m X → S m X
    inverse = Loc.rec (local-S-SC m sc) ηS
    sec-law : (t : L m X) → S-to-L m (inverse t) ≡ t
    sec-law = Unique.≡onη (local-L m X) (S-to-L m ∘ inverse) (idfun _) (λ _ → refl)
    ret-law : (t : S m X) → inverse (S-to-L m t) ≡ t
    ret-law = funExt⁻ (S-unique (separated-S m X)
      (inverse ∘ S-to-L m) (idfun _) (λ _ → refl))

  L-preserves-SC : (m : ℕ) {X : Type} → SC X → SC (L m X)
  L-preserves-SC m sc = isOfHLevelRespectEquiv 0
    (Tr.trunc-respects-≃ 3 (S-to-L m , S-to-L-isEquiv m sc)) (S-preserves-SC m sc)
