{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Descent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Approximation using (finCWmap→CellMap)
open import Cubical.CW.Strictification using (strictCWskel ; elimStrictCW ; strictCwMap≡)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import Cubical.HITs.Pushout using (Pushout)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology using (realisedCW)
open import DeloopS3.Bridge.DMCExactness.Conditional

-- Descend a strict-span comparison to the original continuous maps.
-- CWPushout normalises already-cellular maps; strictCwMap≡ removes this
-- normalisation while retaining the map-compatible comparison.
StrictSpanComparison : Type₁
StrictSpanComparison = (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C))
  → let module P = CWPushout ℓ-zero A B C f g
    in PushoutChainsComparison
      (realisedCW P.B) (realisedCW P.C) (realisedCW P.D)
      (realiseCellMap P.f) (realiseCellMap P.g)
      (Pushout (realiseCellMap P.f) (realiseCellMap P.g) , PT.∣ P.hasCWskelPushout ∣₁)

-- Quantifying over the propositional CW witness prevents a dependence on
-- which finite-pushout construction supplied it.  Crucially the ENTIRE
-- PushoutChainsComparison is transported, including actual-source and
-- actual-sum, not just the homology group equivalences.
SpanComparison : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C) → Type₁
SpanComparison A B C f g = (w : isCW (Pushout f g))
  → PT.∥ PushoutChainsComparison A B C f g (Pushout f g , w) ∥₁

abstract
  realised-CW-path : (A : CW₀) (S : CWskel ℓ-zero)
    → fst A ≃ realise S → realisedCW S ≡ A
  realised-CW-path A S e = Σ≡Prop (λ _ → PT.squash₁) (sym (ua e))

  -- This dependent transport also transports the two actual-map squares.
  -- Its target mentions the original f and g literally; no homology
  -- naturality or compatibility is discarded during descent.
  descend-presentations : (A B C : CW₀) (SA SB SC : CWskel ℓ-zero)
    (ea : fst A ≃ realise SA) (eb : fst B ≃ realise SB) (ec : fst C ≃ realise SC)
    → ((f : realise SA → realise SB) (g : realise SA → realise SC)
       → SpanComparison (realisedCW SA) (realisedCW SB) (realisedCW SC) f g)
    → (f : fst A → fst B) (g : fst A → fst C) → SpanComparison A B C f g
  descend-presentations A B C SA SB SC ea eb ec k =
    subst (λ X → (f : fst X → fst B) (g : fst X → fst C)
      → SpanComparison X B C f g)
      (realised-CW-path A SA ea)
      (subst2 (λ Y Z → (f : realise SA → fst Y) (g : realise SA → fst Z)
        → SpanComparison (realisedCW SA) Y Z f g)
        (realised-CW-path B SB eb) (realised-CW-path C SC ec) k)

module FromStrict (strict-comparison : StrictSpanComparison) where
  private
    abstract
      strict-cellular-comparison : (A B C : CWskel ℓ-zero)
        (f : cellMap (strictCWskel A) (strictCWskel B))
        (g : cellMap (strictCWskel A) (strictCWskel C))
        → SpanComparison (realisedCW (strictCWskel A))
            (realisedCW (strictCWskel B)) (realisedCW (strictCWskel C))
            (realiseCellMap f) (realiseCellMap g)
      strict-cellular-comparison A B C f g =
        subst2 (λ h k → SpanComparison (realisedCW (strictCWskel A))
          (realisedCW (strictCWskel B)) (realisedCW (strictCWskel C))
          (realiseCellMap h) (realiseCellMap k))
          (strictCwMap≡ f) (strictCwMap≡ g)
          (λ w → PT.∣ subst
            (λ v → PushoutChainsComparison
              (realisedCW P.B) (realisedCW P.C) (realisedCW P.D)
              (realiseCellMap P.f) (realiseCellMap P.g)
              (Pushout (realiseCellMap P.f) (realiseCellMap P.g) , v))
            (PT.squash₁ PT.∣ P.hasCWskelPushout ∣₁ w)
            (strict-comparison A B C f g) ∣₁)
        where
        module P = CWPushout ℓ-zero A B C f g

  abstract
    cellular-comparison : (A B C : CWskel ℓ-zero)
      (f : cellMap A B) (g : cellMap A C)
      → SpanComparison (realisedCW A) (realisedCW B) (realisedCW C)
          (realiseCellMap f) (realiseCellMap g)
    cellular-comparison = elimStrictCW λ A → elimStrictCW λ B
      → elimStrictCW λ C → strict-cellular-comparison A B C

    finite-realisation-comparison : (m : ℕ) (A : finCWskel ℓ-zero m)
      (B C : CWskel ℓ-zero)
      (f : realise (finCWskel→CWskel m A) → realise B)
      (g : realise (finCWskel→CWskel m A) → realise C)
      → SpanComparison (realisedCW (finCWskel→CWskel m A))
          (realisedCW B) (realisedCW C) f g
    finite-realisation-comparison m A B C f g w =
      PT.rec2 PT.squash₁
        (λ (h , hp) (k , kp) → subst2
          (λ u v → SpanComparison (realisedCW A') (realisedCW B) (realisedCW C) u v)
          hp kp (cellular-comparison A' B C h k) w)
        (finCWmap→CellMap m A B f) (finCWmap→CellMap m A C g)
      where
      A' : CWskel ℓ-zero
      A' = finCWskel→CWskel m A

    comparison-input : ComparisonInput
    comparison-input A B C f g dA dB dC a b c =
      PT.rec3 PT.squash₁
        (λ (SA , ea) (SB , eb) (SC , ec) →
          descend-presentations A B C
            (finCWskel→CWskel (suc dA) SA)
            (finCWskel→CWskel (suc dB) SB)
            (finCWskel→CWskel (suc dC) SC) ea eb ec
            (finite-realisation-comparison (suc dA) SA
              (finCWskel→CWskel (suc dB) SB)
              (finCWskel→CWskel (suc dC) SC)) f g
            (finite≤→isCW (pushout-finite≤ f g dA dB dC a b c))) a b c
