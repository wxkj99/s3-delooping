{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.DegreeSpan.Map where

open import Cubical.Foundations.Prelude hiding (I)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (Σ; fst; _,_)
open import Cubical.HITs.Pushout.Base using (Pushout; inl; inr; push)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Cover.MarkedDescent.Family using (module FamilyFlattening)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Input.Initial.Endpoint as Init
import DeloopS3.Cert.Input.Initial.Assembly as Ass
import DeloopS3.Cert.Input.Initial.SpanProjection as SP
import DeloopS3.Bridge.OriginalSpan as OS

-- Ordinary component maps, retaining both specified attachment homotopies.
record ContinuousSpanMap (D E : R.Span ℓ-zero ℓ-zero ℓ-zero) : Type₀ where
  field
    overlapMap : R.Span.O D → R.Span.O E
    leftMap : R.Span.L D → R.Span.L E
    rightMap : R.Span.R D → R.Span.R E
    leftSquare : (z : R.Span.O D)
      → leftMap (R.Span.left D z) ≡ R.Span.left E (overlapMap z)
    rightSquare : (z : R.Span.O D)
      → rightMap (R.Span.right D z) ≡ R.Span.right E (overlapMap z)
open ContinuousSpanMap public

totalMap : {D E : R.Span ℓ-zero ℓ-zero ℓ-zero}
  → ContinuousSpanMap D E → R.Total D → R.Total E
totalMap m (inl x) = inl (leftMap m x)
totalMap m (inr y) = inr (rightMap m y)
totalMap m (push z i) =
  (cong inl (leftSquare m z)
    ∙∙ push (overlapMap m z) ∙∙ sym (cong inr (rightSquare m z))) i

-- Seal the constructor comparison with a generic family, before any
-- concrete finite chart or covering classifier is substituted.
private
  module Projected (D E : R.Span ℓ-zero ℓ-zero ℓ-zero)
    (Q : R.Total E → Type₀) where

    flat : R.Span ℓ-zero ℓ-zero ℓ-zero
    R.Span.O flat = Σ (R.Span.O E) (λ z → Q (inl (R.Span.left E z)))
    R.Span.L flat = Σ (R.Span.L E) (λ x → Q (inl x))
    R.Span.R flat = Σ (R.Span.R E) (λ y → Q (inr y))
    R.Span.left flat (z , q) = R.Span.left E z , q
    R.Span.right flat (z , q) = R.Span.right E z , subst Q (push z) q

    module F = FamilyFlattening (R.Span.left E) (R.Span.right E) Q

    module _ (e : R.SpanEquiv D flat) where
      projected : ContinuousSpanMap D E
      overlapMap projected = fst ∘ equivFun (R.SpanEquiv.overlapEquiv e)
      leftMap projected = fst ∘ equivFun (R.SpanEquiv.leftVertex e)
      rightMap projected = fst ∘ equivFun (R.SpanEquiv.rightVertex e)
      leftSquare projected z = cong fst (R.SpanEquiv.leftSquare e z)
      rightSquare projected z = cong fst (R.SpanEquiv.rightSquare e z)

      module P = SP.Prescribed {D = D} {E = flat} e F.projection

      abstract
        agrees : totalMap projected ≡ P.projection
        agrees = funExt pointwise
          where
          pointwise : (x : R.Total D)
            → totalMap projected x ≡ P.projection x
          pointwise (inl x) = refl
          pointwise (inr y) = refl
          pointwise (push z i) j = P.projection-push z (~ j) i

initial-span-map : (c : ShortCase)
  → ContinuousSpanMap (R.diagram (Input.S₀ c)) (Input.BaseSpan c)
initial-span-map c = Projected.projected
  (R.diagram (Input.S₀ c)) (Input.BaseSpan c) (Input.Q c) (Ass.initial-span c)

abstract
  initial-total-agrees : (c : ShortCase)
    → totalMap (initial-span-map c) ≡ Init.initialProjection c
  initial-total-agrees c = Projected.agrees
    (R.diagram (Input.S₀ c)) (Input.BaseSpan c) (Input.Q c) (Ass.initial-span c)

-- Convenient component names with the actual source and target pieces.
πO : (c : ShortCase) → R.O (Input.S₀ c) → R.Span.O (Input.BaseSpan c)
πO c = overlapMap (initial-span-map c)

πL : (c : ShortCase) → R.L (Input.S₀ c) → R.Span.L (Input.BaseSpan c)
πL c = leftMap (initial-span-map c)

πR : (c : ShortCase) → R.R (Input.S₀ c) → R.Span.R (Input.BaseSpan c)
πR c = rightMap (initial-span-map c)

hL : (c : ShortCase) (z : R.O (Input.S₀ c))
  → πL c (R.left (Input.S₀ c) z) ≡ R.Span.left (Input.BaseSpan c) (πO c z)
hL c = leftSquare (initial-span-map c)

hR : (c : ShortCase) (z : R.O (Input.S₀ c))
  → πR c (R.right (Input.S₀ c) z) ≡ R.Span.right (Input.BaseSpan c) (πO c z)
hR c = rightSquare (initial-span-map c)

I : ShortCase → Type₀
I c = R.T (Input.S₀ c)

-- Keep this composite transparent: its forward map is the inverse initial
-- chart applied to precisely the equivalence defining the actual cover.
A≃I : (c : ShortCase) → OS.A c ≃ I c
A≃I c = compEquiv {A = OS.A c} {B = Input.A_G c} {C = I c}
  (OS.sourceCoverEquiv c) (invEquiv (Init.cover-initial c))

πC : (c : ShortCase) → I c → OS.C c
πC c = invEq (Input.originalTotalEquiv c) ∘ Init.initialProjection c

abstract
  initial-over : (c : ShortCase) (a : OS.A c)
    → Init.initialProjection c (equivFun (A≃I c) a) ≡ OS.p-model c a
  initial-over c a = Init.cover-initial-projection c
    (invEq (Init.cover-initial c) (equivFun (OS.sourceCoverEquiv c) a))
    ∙ cong (fst {B = Input.Q c})
        (secEq (Init.cover-initial c) (equivFun (OS.sourceCoverEquiv c) a))

  p-factor : (c : ShortCase)
    → OS.p c ≡ πC c ∘ equivFun (A≃I c)
  p-factor c = funExt λ a →
    cong (invEq (Input.originalTotalEquiv c)) (sym (initial-over c a))

-- Change both legs of the outer span, not only the covering projection.
qI : (c : ShortCase) → I c → OS.R
qI c = OS.q c ∘ invEq (A≃I c)

XI : ShortCase → Type₀
XI c = Pushout (qI c) (Init.initialProjection c)

abstract
  outer-left : (c : ShortCase) (a : OS.A c)
    → OS.q c a ≡ qI c (equivFun (A≃I c) a)
  outer-left c a = cong (OS.q c) (sym (retEq (A≃I c) a))

  outer-right : (c : ShortCase) (a : OS.A c)
    → equivFun (Input.originalTotalEquiv c) (OS.p c a)
      ≡ Init.initialProjection c (equivFun (A≃I c) a)
  outer-right c a = secEq (Input.originalTotalEquiv c) (OS.p-model c a)
    ∙ sym (initial-over c a)

X≃XI : (c : ShortCase) → OS.X c ≃ XI c
X≃XI c = pushoutEquiv
  {A₁ = OS.A c} {B₁ = OS.R} {C₁ = OS.C c}
  {A₂ = I c} {B₂ = OS.R} {C₂ = Input.M_G c}
  (OS.q c) (OS.p c) (qI c) (Init.initialProjection c)
  (A≃I c) (idEquiv OS.R) (Input.originalTotalEquiv c)
  (funExt (outer-left c)) (funExt (outer-right c))
