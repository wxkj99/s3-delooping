{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Integer charts for π₂(RP²) and the LES boundary/transport comparison.
-- TwoCap computes the coefficient -2e in its suspension chart; Pi2Zero
-- proves vanishing from a nonzero image without fixing the stock-chart sign.
module DeloopS3.Seifert.TwistedBundle.Connecting where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Int using (ℤ; pos; _·_; -_; isSetℤ)
open import Cubical.Functions.Embedding
  using (isEmbedding; hasPropFibers→isEmbedding)
open import Cubical.Functions.Fibration using (fiberCong)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction using (characGroupHomℤ)
open import Cubical.HITs.Pushout.Base using (inr)
open import Cubical.HITs.Sn.Base using (S₊; S₊∙)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.HITs.Susp.Base using (north)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.Truncation as TR
open import Cubical.Homotopy.Connected using (isConnectedPath)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base using (π; πGr; πHom; πIso)
open import Cubical.Homotopy.Group.PinSn using (πₙSⁿ≅ℤ; flipSquareIso)
open import Cubical.Homotopy.Group.LES
  using (module πLES; module ΩLES; ΩFibreIso; ←∙∙lCancel-refl-refl)
open import DeloopS3.Move.CancelMinimal using (C; 0C; K; 0K; U; ω; ω₀; mulC)
open import DeloopS3.Sphere.RP2UnitFiber
  using (RP²; q; q-fiber; q-fibers-are-sets)
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Pi2 using (module Homotopy)

-- A map with discrete fibres becomes an embedding on loop spaces.
-- Looping once more is therefore an equivalence. No connectedness or
-- surjectivity assumption on the map is needed for this based assertion.
module DiscreteCover {ℓ ℓ' : Level} {X : Pointed ℓ} {Y : Pointed ℓ'}
  (f : X →∙ Y) (discrete : (y : typ Y) → isSet (fiber (fst f) y)) where

  cong-embedding : (a b : typ X) → isEmbedding (cong (fst f) :> (a ≡ b → fst f a ≡ fst f b))
  cong-embedding a b = hasPropFibers→isEmbedding λ p →
    subst isProp (sym (fiberCong (fst f) p))
      (discrete (fst f b) (a , p) (b , refl))

  loop-embedding : isEmbedding (Ω→ f .fst)
  loop-embedding = J
    (λ y p → isEmbedding (Ω→ {A = X} {B = typ Y , y} (fst f , p) .fst))
    (subst isEmbedding (funExt (λ p → rUnit (cong (fst f) p)))
      (cong-embedding (pt X) (pt X))) (snd f)

embedding-loop-equiv : ∀ {ℓ ℓ'} {X : Pointed ℓ} {Y : Pointed ℓ'}
  (f : X →∙ Y) → isEmbedding (fst f) → isEquiv (Ω→ f .fst)
embedding-loop-equiv {X = X} {Y = Y} f emb = J
  (λ y p → isEquiv (Ω→ {A = X} {B = typ Y , y} (fst f , p) .fst))
  (subst isEquiv (funExt (λ p → rUnit (cong (fst f) p)))
    (emb (pt X) (pt X))) (snd f)

cover-π₂ : ∀ {ℓ ℓ'} {X : Pointed ℓ} {Y : Pointed ℓ'}
  (f : X →∙ Y) → ((y : typ Y) → isSet (fiber (fst f) y))
  → GroupEquiv (πGr 1 X) (πGr 1 Y)
cover-π₂ f discrete .fst = isoToEquiv (ST.setTruncIso
  (equivToIso (_ , embedding-loop-equiv (Ω→ f)
    (DiscreteCover.loop-embedding f discrete))))
cover-π₂ f discrete .snd = πHom 1 f .snd

-- The group of integer charts is a set. Hence the merely set-truncated
-- path supplied by simple connectedness suffices to change sphere basepoint.
sphereChart : (x : S₊ 2) → GroupEquiv (πGr 1 (S₊ 2 , x)) ℤGroup
sphereChart x = TR.rec
  (isSetΣ (isOfHLevel≃ 2 ST.squash₂ isSetℤ)
    (λ _ → isProp→isSet (isPropIsGroupHom _ _)))
  (λ p → compGroupEquiv (πIso (idEquiv _ , sym p) 1)
    (GroupIso→GroupEquiv (πₙSⁿ≅ℤ 1)))
  (isConnectedPath 2 (sphereConnected 2) north x .fst)

-- Choose an actual lift of the cap by its specified false sheet, rather
-- than guessing that q north is judgmentally the cap.
capLift : fiber q (inr tt)
capLift = invEq (q-fiber (inr tt)) false

sphereBase : S₊ 2
sphereBase = capLift .fst

q∙ : (S₊ 2 , sphereBase) →∙ (RP² , inr tt)
q∙ = q , capLift .snd

q-π₂ : GroupEquiv (πGr 1 (S₊ 2 , sphereBase)) (πGr 1 (RP² , inr tt))
q-π₂ = cover-π₂ q∙ q-fibers-are-sets

rp²IntegerGroup : GroupEquiv (πGr 1 (RP² , inr tt)) ℤGroup
rp²IntegerGroup = compGroupEquiv (invGroupEquiv q-π₂) (sphereChart sphereBase)

chart : π 2 (RP² , inr tt) ≃ ℤ
chart = rp²IntegerGroup .fst

-- The library LES has a fixed transpose convention. This lemma exposes it
-- on an actual (untruncated) square; no integer or Euler assumption occurs.
module BoundarySquare {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'}
  (f : X → Y) (x : X) where
  f∙ : (X , x) →∙ (Y , f x)
  f∙ = f , refl

  squareLoop : typ (Ω (Ω (Y , f x)))
    → typ (Ω (fiber f (f x) , (x , refl)))
  squareLoop p i = x , (λ j → p j i)

  boundary-square : (p : typ (Ω (Ω (Y , f x))))
    → πLES.B→fib f∙ 0 .fst ST.∣ p ∣₂ ≡ ST.∣ squareLoop p ∣₂
  boundary-square p = cong ST.∣_∣₂
    (sym (rUnit (Iso.inv (ΩFibreIso f∙)
      (refl , sym (rUnit refl) ∙ p)))
      ∙ (λ k i → x , (λ j → ←∙∙lCancel-refl-refl p k i j)))

module BoundaryTransport (e : ℤ) where
  open Bundle e
  open Homotopy e
  open BoundarySquare pₑ m₀

  -- Cap holonomy is a pointed map; its point proof is exactly the one
  -- already used in Pi2.capFrame∙, including transportRefl and secEq.
  holonomy : Ω (RP² , inr tt) →∙ (C , 0C)
  holonomy .fst p = baseFibre .fst (m₀ , p)
  holonomy .snd = baseFibre-point

  connecting-transport : (p : typ (Ω (Ω (RP² , inr tt))))
    → connectingℤ ST.∣ p ∣₂
      ≡ circleIntegerChart .fst
          ST.∣ Ω→ holonomy .fst (λ i j → p j i) ∣₂
  connecting-transport p = cong
    (λ z → fibreIntegerChart .fst z) (boundary-square p)

-- The transport comparison retains the cap frame and LES transpose convention;
-- it does not identify the signed Euler coefficient in the stock sphere chart.
