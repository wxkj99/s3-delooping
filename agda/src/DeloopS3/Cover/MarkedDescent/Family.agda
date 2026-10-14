{-# OPTIONS --safe --cubical #-}

-- Flatten an ACTUAL family, retaining
-- its transport on push. Used first for the set cover, then for circles.
module DeloopS3.Cover.MarkedDescent.Family where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import DeloopS3.Move.CancelMinimalCore using (EquivOver; ua-equiv-family)

module FamilyFlattening {A L R : Type₀} (f : A → L) (g : A → R)
  (X : Pushout f g → Type₀) where

  O = Pushout f g
  module Flat = FlatteningLemma f g (X ∘ inl) (X ∘ inr)
    (λ a → substEquiv X (push a))

  -- No replacement of the seam by an unspecified homotopic transport.
  comparison : (x : O) → Flat.E x ≃ X x
  comparison (inl l) = idEquiv _
  comparison (inr r) = idEquiv _
  comparison (push a i) = ua-equiv-family (substEquiv X (push a))
    (λ j → X (push a j)) (idEquiv _) (idEquiv _)
    (λ u → subst-filler X (push a) u) i

  Diagram = Pushout Flat.Σf Flat.Σg

  projection : Diagram → O
  projection (inl (l , u)) = inl l
  projection (inr (r , u)) = inr r
  projection (push (a , u) i) = push a i

  flatten : Diagram ≃ Σ O X
  flatten = compEquiv (invEquiv Flat.flatten)
    (Σ-cong-equiv-snd comparison)

  over : EquivOver projection (fst {B = X})
  over .fst = flatten
  over .snd (inl (l , u)) = refl
  over .snd (inr (r , u)) = refl
  over .snd (push (a , u) i) = refl

  lifted-seam : (a : A) (u : X (inl (f a)))
    → PathP (λ i → X (push a i)) u (subst X (push a) u)
  lifted-seam a u i = flatten .fst (push (a , u) i) .snd

  -- This comparison is a dependent path, hence keeps all its instances
  -- on boundary paths; no set truncation of the marking is performed.
  transport-comparison : (a : A) (u : X (inl (f a)))
    → subst X (push a) u ≡ subst X (push a) u
  transport-comparison a u = fromPathP (lifted-seam a u)
