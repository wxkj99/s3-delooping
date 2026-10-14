{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Flatten the actual descended
-- total space, first retaining the coherent quotient-span coordinates.
module DeloopS3.Seifert.TwistedBundle.Flattening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ)
open import Cubical.HITs.Pushout.Base
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Coherent
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)

module Total (e : ℤ) where
  open Bundle e
  open Action e

  ActTotal : Type₁
  ActTotal = Σ QuotientBase actionFamily

  reindex : Mₑ ≃ ActTotal
  reindex = Σ-cong-equiv-fst {B = actionFamily} (invEquiv baseQuotient)

  reindex-back-over : (t : ActTotal)
    → pₑ (invEq reindex t) ≡ baseQuotient .fst (fst t)
  reindex-back-over t = sym (secEq baseQuotient (pₑ (invEq reindex t)))
    ∙ cong (baseQuotient .fst) (cong fst (secEq reindex t))

  L : Type₁
  L = Σ B (λ T → Â T × SignC T)

  R : Type₁
  R = Σ B (λ T → Reg T × SignC T)

  O : Type₁
  O = Σ B (λ T → (Â T × Reg T) × SignC T)

  left : O → L
  left (T , (a , y) , t) = T , a , t

  right : O → R
  right (T , (a , y) , t) = T , y , _+S_ {T = T} t (clutching T a y)

  Filling : Type₁
  Filling = Pushout left right

  FlatSum : Type₁
  FlatSum = Σ B (λ T → Pushout (Fibrewise.Flat.Σf T) (Fibrewise.Flat.Σg T))

  distribute : FlatSum ≃ Filling
  distribute = isoToEquiv (iso to from sec ret)
    where
    to : FlatSum → Filling
    to (T , inl (a , t)) = inl (T , a , t)
    to (T , inr (y , t)) = inr (T , y , t)
    to (T , push ((a , y) , t) i) = push (T , (a , y) , t) i
    from : Filling → FlatSum
    from (inl (T , a , t)) = T , inl (a , t)
    from (inr (T , y , t)) = T , inr (y , t)
    from (push (T , (a , y) , t) i) = T , push ((a , y) , t) i
    sec : (z : Filling) → to (from z) ≡ z
    sec (inl z) = refl
    sec (inr z) = refl
    sec (push z i) = refl
    ret : (z : FlatSum) → from (to z) ≡ z
    ret (T , inl z) = refl
    ret (T , inr z) = refl
    ret (T , push z i) = refl

  fibrewiseTotals : (Σ B (λ T → Σ (SAct T) (FAct T))) ≃ FlatSum
  fibrewiseTotals = Σ-cong-equiv-snd Fibrewise.flattenAction

  fillToAction : Filling ≃ ActTotal
  fillToAction = compEquiv (invEquiv distribute)
    (compEquiv (invEquiv fibrewiseTotals) (invEquiv Σ-assoc-≃))

  coherentBase : Filling → QuotientBase
  coherentBase (inl (T , a , t)) = T , inl a
  coherentBase (inr (T , y , t)) = T , inr y
  coherentBase (push (T , (a , y) , t) i) = T , push (a , y) i

  fillToAction-over : (z : Filling) → fst (fillToAction .fst z) ≡ coherentBase z
  fillToAction-over (inl z) = refl
  fillToAction-over (inr z) = refl
  fillToAction-over (push z i) = refl

  pFill : Filling → RP²
  pFill = baseQuotient .fst ∘ coherentBase

  fillToTotal : Filling ≃ Mₑ
  fillToTotal = compEquiv fillToAction (invEquiv reindex)

  fillToTotal-over : (z : Filling) → pₑ (fillToTotal .fst z) ≡ pFill z
  fillToTotal-over z = reindex-back-over (fillToAction .fst z)
    ∙ cong (baseQuotient .fst) (fillToAction-over z)

  flattenDescent : Mₑ ≃ Filling
  flattenDescent = invEquiv fillToTotal

-- This untruncated equivalence retains the projection. SmallChart and
-- MarkedSeifert.Final.SmallSpan express the span in Ksign, C and A×C coordinates.
