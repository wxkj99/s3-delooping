{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Seifert.MarkedSeifert.DescentChart.L9 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Seifert.TwistedBundle.Base using (A; R; Ksign)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
  using (Kinv; kbase; klein-base; fibre; r; j; r-as-fibre; j-baseProjection)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
  using (based)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third
  using (cong-based)
open import DeloopS3.Seifert.MarkedSeifert.DescentChart
  using (raw; raw-base; raw-fibre; raw-over; F; F₀; V; bCircle; τ;
         based-conjugate; prepend-dependent)

-- The entire calculation is done with a variable map.  In particular, no
-- equivalence implementation, descended family, or HIT recursor is unfolded.
-- Retaining the two homotopies in the *types* avoids composing a large
-- concrete pointing with refl and then cancelling that extra unit.
module Markings
  {ℓX ℓY ℓC ℓB ℓD : Level}
  (X : Type ℓX) (Y : Type ℓY) (C₀ : Type ℓC)
  (B₀ : Type ℓB) (D₀ : Type ℓD)
  (f : X → Y) (s : C₀ → X) (t : C₀ → Y)
  (π : Y → B₀) (q : X → D₀) (b : D₀ → B₀)
  (c : C₀) (k : X) (p : k ≡ s c)
  (fibre-computation : (u : C₀) → f (s u) ≡ t u)
  (over-computation : (z : X) → π (f z) ≡ b (q z)) where

  opaque
    -- The cancellation in based-conjugate is proved by path induction in
    -- DescentChart.  All its endpoints here are small, abstract parameters.
    mark-fibre : (v : c ≡ c) (l : k ≡ k)
      → l ≡ (p ∙ cong s v) ∙ sym p
      → PathP (λ i → fibre-computation c i ≡ fibre-computation c i)
          (based {X = Y} {a = f k} {b = f (s c)}
            (cong f p) (cong f l))
          (cong t v)
    mark-fibre v l computation = prepend-dependent
      (λ i → fibre-computation c i ≡ fibre-computation c i)
      (based {X = Y} {a = f k} {b = f (s c)} (cong f p) (cong f l))
      (cong (f ∘ s) v) (cong t v)
      (sym (cong-based f {a = k} {b = s c} p l)
        ∙ cong (cong f)
          (cong (based {X = X} {a = k} {b = s c} p) computation
            ∙ based-conjugate {X = X} {x = k} {y = s c} p (cong s v)))
      (λ i h → fibre-computation (v h) i)

    mark-projection : (l : k ≡ k) (v : q (s c) ≡ q (s c))
      → based {X = D₀} {a = q k} {b = q (s c)}
          (cong q p) (cong q l) ≡ v
      → PathP (λ i → over-computation (s c) i ≡ over-computation (s c) i)
          (cong π (based {X = Y} {a = f k} {b = f (s c)}
            (cong f p) (cong f l)))
          (cong b v)
    mark-projection l v computation = prepend-dependent
      (λ i → over-computation (s c) i ≡ over-computation (s c) i)
      (cong π (based {X = Y} {a = f k} {b = f (s c)}
        (cong f p) (cong f l)))
      (cong (π ∘ f) (based {X = X} {a = k} {b = s c} p l))
      (cong b v)
      (cong (cong π) (sym (cong-based f {a = k} {b = s c} p l)))
      (symP (prepend-dependent
        (λ i → over-computation (s c) (~ i) ≡ over-computation (s c) (~ i))
        (cong b v)
        (cong (b ∘ q) (based {X = X} {a = k} {b = s c} p l))
        (cong (π ∘ f) (based {X = X} {a = k} {b = s c} p l))
        (sym (cong (cong b)
          (cong-based q {a = k} {b = s c} p l ∙ computation)))
        (λ i h → over-computation (based {X = X} {a = k} {b = s c} p l h) (~ i))))

-- Only the computation homotopies reduce here: raw-fibre at zero
-- and raw-over at (base , 0C) are reflexivity.  The generic proofs remain
-- opaque; their f parameter is never definitionally evaluated.
private
  module Actual (a : A) = Markings
    Kinv Ksign C R S¹ (raw a .fst) fibre (F a)
    fst fst (bCircle a) 0C kbase klein-base (raw-fibre a) (raw-over a)

opaque
  raw-r : (a : A)
    → based {X = Ksign} {a = raw a .fst kbase} {b = F₀ a}
        (raw-base a) (cong (raw a .fst) r) ≡ V a hC
  raw-r a = Actual.mark-fibre a hC r r-as-fibre

  raw-j-projects : (a : A)
    → cong (λ (z : Ksign) → fst z)
        (based {X = Ksign} {a = raw a .fst kbase} {b = F₀ a}
          (raw-base a) (cong (raw a .fst) j)) ≡ τ a
  raw-j-projects a = Actual.mark-projection a j (sym loop) j-baseProjection
