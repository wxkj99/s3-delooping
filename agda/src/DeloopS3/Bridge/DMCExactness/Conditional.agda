{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Conditional where

-- Construct the geometric pushout LES from a map-compatible comparison.
-- PrismChains.Packaging supplies ComparisonInput for finite CW spans,
-- retaining the original maps and both induced homology squares.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.CW.Base using (realise)
open import Cubical.HITs.Pushout using (Pushout)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.DMCExactness.Comparison

-- Factor through ComparisonData on abstract groups to avoid unfolding
-- cellular approximation during record elaboration.
PushoutChainsComparison : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (P : CW₀) → Type₁
PushoutChainsComparison A B C f g P = Σ[ p ∈ (fst P ≡ Pushout f g) ]
  Σ[ d ∈ ComparisonData (H̃ᶜʷ A) (H̃ᶜʷ B) (H̃ᶜʷ C) (H̃ᶜʷ P)
    (actual-source A B C f g) (actual-sum A B C f g P p) ]
  (fst P ≃ realise (ComparisonData.pushoutSkel d))

abstract
  comparison→LES : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C) (P : CW₀)
    → PushoutChainsComparison A B C f g P → GeometricPushoutLES A B C f g P
  comparison→LES A B C f g P (p , d , r) = p ,
    comparison→sequence (H̃ᶜʷ A) (H̃ᶜʷ B) (H̃ᶜʷ C) (H̃ᶜʷ P)
      (actual-source A B C f g) (actual-sum A B C f g P p) d

  -- Only expose the boundary field of the existing LES constructor.
  comparison→LES-boundary-β : (A B C : CW₀)
    (f : fst A → fst B) (g : fst A → fst C) (P : CW₀)
    (c : PushoutChainsComparison A B C f g P) (n : ℕ)
    → SpanSequenceData.boundary (snd (comparison→LES A B C f g P c)) n
     ≡ SpanSequenceData.boundary
         (comparison→sequence (H̃ᶜʷ A) (H̃ᶜʷ B) (H̃ᶜʷ C) (H̃ᶜʷ P)
           (actual-source A B C f g) (actual-sum A B C f g P (fst c))
           (fst (snd c))) n
  comparison→LES-boundary-β A B C f g P (p , d , r) n = refl

ComparisonInput : Type₁
ComparisonInput = (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (dA dB dC : ℕ) (a : Finite≤ dA (fst A)) (b : Finite≤ dB (fst B)) (c : Finite≤ dC (fst C))
  → PT.∥ PushoutChainsComparison A B C f g
    (Pushout f g , finite≤→isCW (pushout-finite≤ f g dA dB dC a b c)) ∥₁

-- Here PushoutLES denotes the geometric record, unlike LES.PushoutLES.
-- The comparison, CW witnesses, and cellular approximations remain under
-- one propositional truncation.
module Conditional (pushout-chains-input : ComparisonInput) where
  PushoutLES : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C) (P : CW₀) → Type₁
  PushoutLES = GeometricPushoutLES

  finite-pushoutLES-merely : (A B C : CW₀)
    (f : fst A → fst B) (g : fst A → fst C)
    (dA dB dC : ℕ)
    (a : Finite≤ dA (fst A)) (b : Finite≤ dB (fst B))
    (c : Finite≤ dC (fst C))
    → PT.∥ PushoutLES A B C f g
        (Pushout f g , finite≤→isCW (pushout-finite≤ f g dA dB dC a b c)) ∥₁
  finite-pushoutLES-merely A B C f g dA dB dC a b c =
    PT.map (comparison→LES A B C f g
      (Pushout f g , finite≤→isCW (pushout-finite≤ f g dA dB dC a b c)))
      (pushout-chains-input A B C f g dA dB dC a b c)
