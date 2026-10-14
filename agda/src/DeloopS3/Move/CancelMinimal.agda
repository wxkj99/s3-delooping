{-# OPTIONS --safe --cubical #-}

-- Marked cancellation and fibre comparison for the identity-leg model.
-- Only the primitive identity-leg/minimal model; no general graph move.
module DeloopS3.Move.CancelMinimal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Int using (ℤ; pos; ·IdR)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.Group.Instances.Int using (ℤHom)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase; emloop)
open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; 0ₖ)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
  using (_+ₖ_; addIso)
open import Cubical.Homotopy.EilenbergMacLane.Properties
  using (EM≃ΩEM+1; EM→ΩEM+1-0ₖ; EM→ΩEM+1-hom; inducedFun-EM₁)
open import DeloopS3.Move.CancelMinimalCore public
open import DeloopS3.Move.CancelLoopCell public

C K : Type₀
C = EM ℤAbGroup 1
K = EM ℤAbGroup 2

0C : C
0C = 0ₖ {G = ℤAbGroup} 1

0K : K
0K = 0ₖ {G = ℤAbGroup} 2

T² : Type₀
T² = C × C

_+C_ : C → C → C
_+C_ = _+ₖ_ {G = ℤAbGroup} {n = 1}

-- The actual map induced by n ↦ s*n, not just its degree.
mulC : ℤ → C → C
mulC s = inducedFun-EM₁ (ℤHom s)

ω : C ≃ (0K ≡ 0K)
ω = EM≃ΩEM+1 {G = ℤAbGroup} 1

ω₀ : ω .fst 0C ≡ refl
ω₀ = EM→ΩEM+1-0ₖ {G = ℤAbGroup} 1

ω-add : (t u : C) → ω .fst (t +C u) ≡ ω .fst t ∙ ω .fst u
ω-add = EM→ΩEM+1-hom {G = ℤAbGroup} 1

U : K → Type₀
U k = 0K ≡ k

Tot : {X : Type₀} → (X → K) → Type₀
Tot {X} c = Σ X (U ∘ c)

transport-U : {k l : K} (p : k ≡ l) (u : U k)
  → transport (cong U p) u ≡ u ∙ p
transport-U = transport-path-right 0K

-- The primitive loop--cell cancellation over K, with an arbitrary seam.
-- Its slice homotopy is α on the graph, refl on the cap, and α(i∨j)
-- on the seam.
module Primitive (α : C → 0K ≡ 0K) where
  open PrimitiveLoopCell 0K α public

! : C → Unit
! _ = tt

O : Type₀
O = Pushout (idfun C) !

module Minimal (s : ℤ) where
  bₛ : T² → C
  bₛ (a , t) = t +C mulC s a

  Eₛ : Type₀
  Eₛ = Pushout (idfun T²) bₛ

  πₛ : Eₛ → O
  πₛ (inl (a , t)) = inl a
  πₛ (inr t) = inr tt
  πₛ (push (a , t) i) = push a i

  rotₛ : (a : C) → C ≃ C
  rotₛ a = isoToEquiv (addIso {G = ℤAbGroup} 1 (mulC s a))

  module Flat = FlatteningLemma (idfun C) ! (λ _ → C) (λ _ → C) rotₛ

  -- Flat.E has exactly the three clauses: C, C, ua (rotₛ a).
  Dₛ : O → Type₀
  Dₛ = Flat.E

  -- The library's right vertex is Σ Unit (λ _ → C), so remove its
  -- literal Unit coordinate.  All three clauses preserve the projection.
  flatten-chart : Pushout Flat.Σf Flat.Σg ≃ Eₛ
  flatten-chart = isoToEquiv (iso f g fg gf)
    where
    f : Pushout Flat.Σf Flat.Σg → Eₛ
    f (inl z) = inl z
    f (inr (tt , t)) = inr t
    f (push z i) = push z i

    g : Eₛ → Pushout Flat.Σf Flat.Σg
    g (inl z) = inl z
    g (inr t) = inr (tt , t)
    g (push z i) = push z i

    fg : (z : Eₛ) → f (g z) ≡ z
    fg (inl z) = refl
    fg (inr t) = refl
    fg (push z i) = refl

    gf : (z : Pushout Flat.Σf Flat.Σg) → g (f z) ≡ z
    gf (inl z) = refl
    gf (inr (tt , t)) = refl
    gf (push z i) = refl

  flatten-min : Σ O Dₛ ≃ Eₛ
  flatten-min = compEquiv Flat.flatten flatten-chart

  αₛ : C → (0K ≡ 0K)
  αₛ a = ω .fst (mulC s a)

  -- cₛ, h, and ηₛ are the literal pushout clauses in the generic
  -- PrimitiveLoopCell module; none of the shear data are discarded.
  open Primitive αₛ public hiding (O)
    renaming (c to cₛ; η to ηₛ)

  R1-min : EquivOver cₛ (λ (_ : Unit) → 0K)
  R1-min = primitive-loop-cell-cancel

  -- Exactly ω-add followed by inverse transport-U.
  seam-naturality : (a t : C)
    → ω .fst (t +C mulC s a)
      ≡ transport (cong U (αₛ a)) (ω .fst t)
  seam-naturality a t = ω-add t (mulC s a)
    ∙ sym (transport-U (αₛ a) (ω .fst t))

  family-min : (z : O) → Dₛ z ≃ U (cₛ z)
  family-min (inl a) = ω
  family-min (inr tt) = ω
  family-min (push a i) = ua-equiv-family (rotₛ a)
    (λ i → U (αₛ a i)) ω ω
    (λ t → toPathP (sym (seam-naturality a t))) i

  total-min : Eₛ ≃ Tot cₛ
  total-min = compEquiv (invEquiv flatten-min) (Σ-cong-equiv-snd family-min)

  total-min-over : (z : Eₛ) → total-min .fst z .fst ≡ πₛ z
  total-min-over (inl z) = refl
  total-min-over (inr t) = refl
  total-min-over (push z i) = refl

  -- The direct total-space cancellation and its specified square.
  open IdentityCancellation bₛ public
    renaming (r to rₛ; j to jₛ; rj to rjₛ; jr to jrₛ; cancel to total-cancel)

  -- Forward cancellation sends the graph coordinate to +s, not -s.
  graph-transport : (a t : C)
    → transport (cong U (ηₛ (inl a))) (ω .fst t)
      ≡ ω .fst (rₛ (inl (a , t)))
  graph-transport a t = sym (seam-naturality a t)

  total-marked-cancel : Tot cₛ ≃ (Unit × U 0K)
  total-marked-cancel = Σ-over-equiv U R1-min

  -- The minimum example is valid for every s, including nonzero ones.
  marked-total-circle : Tot cₛ ≃ C
  marked-total-circle = compEquiv total-marked-cancel
    (compEquiv (ΣUnit (λ _ → U 0K)) (invEquiv ω))

  -- The fibre comparison induced by ηₛ agrees with rₛ, not
  -- merely with some equivalence of the underlying total-space types.
  marked-cap : (t : C)
    → marked-total-circle .fst (total-min .fst (inr t)) ≡ t
  marked-cap t = cong (invEq ω) (transportRefl (ω .fst t)) ∙ retEq ω t

  marked-agrees-direct : (z : Eₛ)
    → marked-total-circle .fst (total-min .fst z) ≡ rₛ z
  marked-agrees-direct z =
    cong (marked-total-circle .fst ∘ total-min .fst) (sym (jrₛ z))
    ∙ marked-cap (rₛ z)

  -- The equivalence Eₛ ≃ O×C over O.
  total-trivialization : Eₛ ≃ (O × C)
  total-trivialization = compEquiv total-min
    (Σ-cong-equiv-snd (λ z → compEquiv
      (pathToEquiv (cong U (ηₛ z))) (invEquiv ω)))

  trivialization-formula : (z : Eₛ)
    → total-trivialization .fst z ≡ (πₛ z , rₛ z)
  trivialization-formula z i = total-min-over z i , marked-agrees-direct z i

  -- The actual boundary-loop computations [s,1], with positive sign.
  graph-winding : cong (λ a → rₛ (inl (a , 0C))) (emloop (pos 1)) ≡ emloop s
  graph-winding = cong emloop (·IdR s)

  fibre-winding : cong (λ t → rₛ (inl (0C , t))) (emloop (pos 1)) ≡ emloop (pos 1)
  fibre-winding = refl

-- A concrete nonzero-shear instance, with all its constructions available.
module NonzeroShear = Minimal (pos 1)

-- Cancellation specialised to the marking target of the minimal test.  This is
-- primitive cancellation only, not the general graph/attachment move.
module MarkedPrimitive {ℓ : Level} (Q : Type ℓ) (q : Q)
  (L R : q ≡ q) (ε : Sign) where
  open PrimitiveCancellation Q q L R ε public

  primitive-cancel-over-K : (m : V → K) → EquivOver m (m ∘ j)
  primitive-cancel-over-K = primitive-cancel-over
