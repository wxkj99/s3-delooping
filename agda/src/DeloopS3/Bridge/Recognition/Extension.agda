{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Extension where

-- Moore extensions from merely nullhomotopic degree composites.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat
open import Cubical.HITs.Pushout.Base using (inl ; inr ; push)
open import DeloopS3.Local.Powers using (SphereFromCircle ; degSphere)
open import DeloopS3.Local.EI public using (Moore ; BottomMoore ; TopMoore)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetTruncation as ST

extend-moore : {X : Type} (d n : ℕ)
  (s : SphereFromCircle n → X) (x : X)
  → PT.∥ s ∘ degSphere d n ≡ (λ _ → x) ∥₁
  → PT.∥ Σ[ f ∈ (Moore d n → X) ] (f ∘ inr ≡ s) ∥₁
extend-moore {X} d n s x = PT.map λ h → extend h , refl
  where
  extend : s ∘ degSphere d n ≡ (λ _ → x) → Moore d n → X
  extend h (inl _) = x
  extend h (inr a) = s a
  extend h (push a i) = h (~ i) a

-- Effectiveness converts equality of set-truncated maps to a merely
-- existing nullhomotopy, without selecting an untruncated witness.
extend-moore-from-class : {X : Type} (d n : ℕ)
  (s : SphereFromCircle n → X) (x : X)
  → ST.∣ s ∘ degSphere d n ∣₂ ≡ ST.∣ (λ _ → x) ∣₂
  → PT.∥ Σ[ f ∈ (Moore d n → X) ] (f ∘ inr ≡ s) ∥₁
extend-moore-from-class d n s x p =
  extend-moore d n s x (Iso.fun ST.PathIdTrunc₀Iso p)
