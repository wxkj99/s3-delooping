{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Geometry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ ; _+_)
open import Cubical.Data.Sigma
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Approximation using (finCWmap→CellMap)
open import Cubical.CW.Strictification using (strictCWskel ; strict≡ ; strictCwMap≡)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import Cubical.HITs.Pushout using (Pushout ; pushoutEquiv)
import Cubical.HITs.PropositionalTruncation as PT

-- Strictification preserves the specified stabilisation stage, not merely
-- the proposition that some finite-dimensional model exists.
strict-finite-skeleton : (m : ℕ) → finCWskel ℓ-zero m → finCWskel ℓ-zero m
strict-finite-skeleton m A = fst S , snd S , stable
  where
  A' : CWskel ℓ-zero
  A' = finCWskel→CWskel m A
  S : CWskel ℓ-zero
  S = strictCWskel A'
  stable : (k : ℕ) → isEquiv (CW↪ S (k + m))
  stable = subst (λ X → (k : ℕ) → isEquiv (CW↪ X (k + m)))
    (sym (strict≡ A')) (snd (snd A))

abstract
  strict-realisation-equiv : (S : CWskel ℓ-zero)
    → realise S ≃ realise (strictCWskel S)
  strict-realisation-equiv S = pathToEquiv (cong realise (sym (strict≡ S)))

  -- This is a full, all-stage cellular approximation with a specified
  -- global homotopy, unlike CWmap→finCellMap at an individual finite window.
  finite-strict-approximation : (m : ℕ) (A : finCWskel ℓ-zero m)
    (B : CWskel ℓ-zero)
    (u : realise (strictCWskel (finCWskel→CWskel m A)) → realise (strictCWskel B))
    → PT.∥ Σ[ h ∈ cellMap (strictCWskel (finCWskel→CWskel m A)) (strictCWskel B) ]
        (realiseCellMap h ≡ u) ∥₁
  finite-strict-approximation m A B u =
    finCWmap→CellMap m (strict-finite-skeleton m A) (strictCWskel B) u

-- An explicit geometric model for an arbitrary original span.  The vertex
-- equivalences can be the chosen finite CW presentations followed by
-- strict-realisation-equiv.  These squares retain the original f and g.
module Model {A B C : Type} (f : A → B) (g : A → C)
  (SA SB SC : CWskel ℓ-zero)
  (ea : A ≃ realise (strictCWskel SA))
  (eb : B ≃ realise (strictCWskel SB))
  (ec : C ≃ realise (strictCWskel SC))
  (h : cellMap (strictCWskel SA) (strictCWskel SB))
  (k : cellMap (strictCWskel SA) (strictCWskel SC))
  (hp : realiseCellMap h ≡ fst eb ∘ f ∘ invEq ea)
  (kp : realiseCellMap k ≡ fst ec ∘ g ∘ invEq ea) where

  module P = CWPushout ℓ-zero SA SB SC h k

  abstract
    left-square : fst eb ∘ f ≡ realiseCellMap P.f ∘ fst ea
    left-square = funExt λ x → sym
      (cong (λ v → realiseCellMap v (fst ea x)) (strictCwMap≡ h)
        ∙ funExt⁻ hp (fst ea x)
        ∙ cong (fst eb ∘ f) (retEq ea x))

    right-square : fst ec ∘ g ≡ realiseCellMap P.g ∘ fst ea
    right-square = funExt λ x → sym
      (cong (λ v → realiseCellMap v (fst ea x)) (strictCwMap≡ k)
        ∙ funExt⁻ kp (fst ea x)
        ∙ cong (fst ec ∘ g) (retEq ea x))

    pushout-span-equiv : Pushout f g
      ≃ Pushout (realiseCellMap P.f) (realiseCellMap P.g)
    pushout-span-equiv = pushoutEquiv f g
      (realiseCellMap P.f) (realiseCellMap P.g) ea eb ec left-square right-square

    pushout-realisation-equiv : Pushout f g ≃ realise P.pushoutSkel
    pushout-realisation-equiv = compEquiv pushout-span-equiv (snd P.hasCWskelPushout)
