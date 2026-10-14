{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Rechart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using
  (_≃_ ; idEquiv ; invEquiv ; secEq ; retEq ; equivEq ; invEquivIdEquiv)
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.Pushout.Base using (cofib ; inl ; inr ; push)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)

module Rechart {A A' B B' : Type}
  (s : A' ≃ A) (t : B ≃ B') (f : A → B) where

  g : A' → B'
  g = fst t ∘ f ∘ fst s

  forward : cofib f ≃ cofib g
  forward = pushoutEquiv (λ _ → tt) f (λ _ → tt) g
    (invEquiv s) (idEquiv Unit) t refl
    (funExt λ x → cong (fst t ∘ f) (sym (secEq s x)))

  backward : cofib g ≃ cofib f
  backward = pushoutEquiv (λ _ → tt) g (λ _ → tt) f
    s (idEquiv Unit) (invEquiv t) refl
    (funExt λ x → retEq t (f (fst s x)))

abstract
  identity-rechart : {A B : Type} (f : A → B)
    → Path (cofib f ≃ cofib f)
        (pushoutEquiv (λ _ → tt) f (λ _ → tt) f
          (idEquiv A) (idEquiv Unit) (idEquiv B) refl refl)
        (idEquiv (cofib f))
  identity-rechart {A} {B} f = equivEq (funExt h)
    where
    h : (x : cofib f)
      → Path (cofib f)
          (fst (pushoutEquiv (λ _ → tt) f (λ _ → tt) f
            (idEquiv A) (idEquiv Unit) (idEquiv B) refl refl) x)
          x
    h (inl tt) = refl
    h (inr b) = refl
    h (push a i) j = sym (rUnit (push a)) j i

  forward-id : {A B : Type} (f : A → B)
    → Path (cofib f ≃ cofib f)
        (Rechart.forward (idEquiv A) (idEquiv B) f)
        (idEquiv (cofib f))
  forward-id {A} {B} f = equivEq (funExt h)
    where
    h : (x : cofib f)
      → Path (cofib f)
          (fst (Rechart.forward (idEquiv A) (idEquiv B) f) x)
          x
    h (inl tt) = refl
    h (inr b) = refl
    h (push a i) j = sym (rUnit (push a)) j i

  backward-id : {A B : Type} (f : A → B)
    → Path (cofib f ≃ cofib f)
        (Rechart.backward (idEquiv A) (idEquiv B) f)
        (idEquiv (cofib f))
  backward-id {A} {B} f = equivEq (funExt h)
    where
    h : (x : cofib f)
      → Path (cofib f)
          (fst (Rechart.backward (idEquiv A) (idEquiv B) f) x)
          x
    h (inl tt) = refl
    h (inr b) = refl
    h (push a i) j = sym (rUnit (push a)) j i

  cofibre-rechart-inverse : {A A' B B' : Type}
    (s : A' ≃ A) (t : B ≃ B') (f : A → B)
    → Path (cofib f ≃ cofib (Rechart.g s t f))
        (Rechart.forward s t f)
        (invEquiv (Rechart.backward s t f))
  cofibre-rechart-inverse {A} {A'} {B} {B'} s t f =
    EquivJ
      (λ B t → (f : A → B)
        → Path (cofib f ≃ cofib (Rechart.g s t f))
            (Rechart.forward s t f)
            (invEquiv (Rechart.backward s t f)))
      (λ f → EquivJ
        (λ A' s → Path (cofib f ≃ cofib (Rechart.g s (idEquiv B') f))
          (Rechart.forward s (idEquiv B') f)
          (invEquiv (Rechart.backward s (idEquiv B') f)))
        (forward-id f
          ∙ sym (cong invEquiv (backward-id f)
            ∙ invEquivIdEquiv (cofib f)))
        s)
      t f
