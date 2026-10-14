{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The actual four-edge cycle of the twisted-bundle chart.
-- This module does not replace Base.fA with a different chart.
module DeloopS3.Seifert.TwistedBundle.Chart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Univalence using (ua-gluePath)
open import Cubical.Foundations.GroupoidLaws using (cong-∙; assoc)
open import Cubical.Foundations.Path
  using (compPath→Square; compPathl-cancel; compPathr-cancel)
open import Cubical.Foundations.HLevels
  using (isSet→SquareP; isPropIsSet; isOfHLevelRespectEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Bool
  using (Bool; false; true; not; _⊕_; ¬false→true; not≢const; isSetBool)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.RPn.Base using (RP; cov⁻¹; Bool*; 2-EltType₀)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Seifert.TwistedBundle.Torsor
  using (frame; frame-self; frame-op; op)
open import DeloopS3.Seifert.TwistedBundle.Base using (R; A; w₁; pr₁; δ; fA)
open import DeloopS3.Move.CancelMinimal using (C; 0C)

-- These comparisons are propositional: the library's torsor frame must
-- not be assumed to reduce judgmentally to Boolean xor.
abstract
  frame-other : (y : Bool) → frame Bool* y .fst (not y) ≡ true
  frame-other y = ¬false→true (frame Bool* y .fst (not y)) λ q →
    not≢const y (invEq (congEquiv (frame Bool* y))
      (q ∙ sym (frame-self Bool* y)))

  frame-bool : (y z : Bool) → frame Bool* y .fst z ≡ y ⊕ z
  frame-bool false false = frame-self Bool* false
  frame-bool false true = frame-other false
  frame-bool true false = frame-other true
  frame-bool true true = frame-self Bool* true

  op-bool : (y : Bool) → op Bool* y ≡ not y
  op-bool y = invEq (congEquiv (frame Bool* y))
    (frame-op Bool* y ∙ sym (frame-other y))

L Rv : Bool → A
L z = inl (inr tt) , z
Rv z = inr tt , z

L₀ L₁ R₀ R₁ : A
L₀ = L false
L₁ = L true
R₀ = Rv false
R₁ = Rv true

E : (y z : Bool) → L z ≡ Rv (y ⊕ z)
E y z i = push (inr tt , y) i ,
  ua-gluePath (frame Bool* y) (frame-bool y z) i

-- Parenthesization keeps the two half-cycles explicit.
w : L₀ ≡ L₀
w = (E false false ∙ sym (E true true))
  ∙ (E false true ∙ sym (E true false))

a : Bool → pr₁ L₀ ≡ pr₁ R₀
a y = push (inr tt , y)

t : pr₁ L₀ ≡ pr₁ L₀
t = a false ∙ sym (a true)

w-projects : cong pr₁ w ≡ t ∙ t
w-projects = cong-∙ pr₁
    (E false false ∙ sym (E true true))
    (E false true ∙ sym (E true false))
  ∙ cong₂ _∙_
      (cong-∙ pr₁ (E false false) (sym (E true true)))
      (cong-∙ pr₁ (E false true) (sym (E true false)))

δ-L : (z : Bool) → δ (L z) ≡ L (not z)
δ-L z = ΣPathP (refl , op-bool z)

δ-R : (z : Bool) → δ (Rv z) ≡ Rv (not z)
δ-R z = ΣPathP (refl , op-bool z)

-- Elimination by the four vertices and four edges. Flattening supplies
-- the coverage of the actual dependent total space, not a replacement A.
private
  module Flat = FlatteningLemma
    (λ (a : Σ (RP 0) (λ x → fst (cov⁻¹ 0 x))) → fst a)
    (λ _ → tt)
    (λ x → fst (cov⁻¹ 0 x)) (λ (_ : Unit) → Bool)
    (λ a → frame (cov⁻¹ 0 (fst a)) (snd a))

  -- The two families agree constructorwise, not definitionally at a
  -- variable base point (the same adapter occurs in TotalCov≃Sn).
  cover≃Flat : (x : R) → fst (w₁ x) ≃ Flat.E x
  cover≃Flat (inl x) = idEquiv _
  cover≃Flat (inr x) = idEquiv _
  cover≃Flat (push a i) = idEquiv _

  toFlat : A → Σ R Flat.E
  toFlat (x , z) = x , cover≃Flat x .fst z

  fromFlat : Σ R Flat.E → A
  fromFlat (x , z) = x , invEq (cover≃Flat x) z

  from-to : (a : A) → fromFlat (toFlat a) ≡ a
  from-to (inl x , z) = refl
  from-to (inr x , z) = refl
  from-to (push a i , z) = refl

  -- At j=0 this is the literal flattening edge; at j=1 it is E.
  E-adjust : (y z : Bool) (j : I)
    → L z ≡ Rv (frame-bool y z j)
  E-adjust y z j i = push (inr tt , y) i ,
    ua-gluePath (frame Bool* y) (λ k → frame-bool y z (k ∧ j)) i

chartElim : ∀ {ℓ} (P : A → Type ℓ)
  → (l : (z : Bool) → P (L z))
  → (r : (z : Bool) → P (Rv z))
  → ((y z : Bool) → PathP (λ i → P (E y z i)) (l z) (r (y ⊕ z)))
  → (a : A) → P a
chartElim P l r e a = subst P (from-to a)
  (subst (λ x → P (fromFlat x)) (Flat.FlattenIso.fwd-bwd (toFlat a))
    (onFlat (Flat.FlattenIso.bwd (toFlat a))))
  where
  onFlat : (x : Pushout Flat.Σf Flat.Σg) → P (fromFlat (Flat.FlattenIso.fwd x))
  onFlat (inl (inr tt , z)) = l z
  onFlat (inr (tt , z)) = r z
  onFlat (push ((inr tt , y) , z) i) = transport
    (λ j → PathP (λ k → P (E-adjust y z (~ j) k))
      (l z) (r (frame-bool y z (~ j)))) (e y z) i

private
  -- The rotated edge, with its right endpoint expressed as not (y ⊕ z).
  rotated-fibre : (y z : Bool)
    → PathP (λ i → fst (w₁ (push (inr tt , y) i)))
        (not z) (not (y ⊕ z))
  rotated-fibre false false i = E false true i .snd
  rotated-fibre false true i = E false false i .snd
  rotated-fibre true false i = E true true i .snd
  rotated-fibre true true i = E true false i .snd

  rotated-E : (y z : Bool) → L (not z) ≡ Rv (not (y ⊕ z))
  rotated-E y z i = push (inr tt , y) i , rotated-fibre y z i

  carrier-set : (T : 2-EltType₀) → isSet (fst T)
  carrier-set T = PT.rec isPropIsSet
    (λ e → isOfHLevelRespectEquiv 2 (invEquiv e) isSetBool) (snd T)

abstract
  -- Deck naturality of every edge, including the actual torsor paths.
  -- Only the discrete cover fibre is used for this square filler.
  δ-E : (y z : Bool)
    → Square (δ-L z) (δ-R (y ⊕ z)) (cong δ (E y z)) (rotated-E y z)
  δ-E y z i j = push (inr tt , y) i ,
    isSet→SquareP (λ i j → carrier-set (w₁ (push (inr tt , y) i)))
      (op-bool z) (op-bool (y ⊕ z))
      (λ i → op (w₁ (E y z i .fst)) (E y z i .snd))
      (rotated-fibre y z) i j

-- Move backwards by half of the four-edge cycle. Applying the chart
-- spanning-tree map gives refl, refl, -loop, -loop at L₀,R₀,L₁,R₁.
-- For the existing library fA we retain the images of these paths instead
-- of asserting that its vertex or edge computations are judgmental.
half-L : (z : Bool) → L (not z) ≡ L z
half-L false = E true true ∙ sym (E false false)
half-L true = E true false ∙ sym (E false true)

half-R : (z : Bool) → Rv (not z) ≡ Rv z
half-R false = sym (E false true) ∙ E true true
half-R true = sym (E false false) ∙ E true false

private
  half-edge-word : (y z : Bool)
    → rotated-E y z ∙ half-R (y ⊕ z) ≡ half-L z ∙ E y z
  half-edge-word false false =
    compPathl-cancel (E false true) (E true true)
    ∙ sym (compPathr-cancel (E false false) (E true true))
  half-edge-word false true =
    compPathl-cancel (E false false) (E true false)
    ∙ sym (compPathr-cancel (E false true) (E true false))
  half-edge-word true false =
    assoc (E true true) (sym (E false false)) (E true false)
  half-edge-word true true =
    assoc (E true false) (sym (E false true)) (E true true)

  half-edge : (y z : Bool)
    → Square (half-L z) (half-R (y ⊕ z)) (rotated-E y z) (E y z)
  half-edge y z = compPath→Square (half-edge-word y z)

abstract
  deck-homotopy : (a : A) → δ a ≡ a
  deck-homotopy = chartElim (λ a → δ a ≡ a)
    (λ z → δ-L z ∙ half-L z)
    (λ z → δ-R z ∙ half-R z)
    (λ y z → δ-E y z ∙₂ half-edge y z)

  -- Retain the actual vertex beta path before applying fA.
  deck-L : (z : Bool)
    → deck-homotopy (L z) ≡ δ-L z ∙ half-L z
  deck-L z = transportRefl _ ∙ transportRefl (δ-L z ∙ half-L z)

  H : (a : A) → fA .fst (δ a) ≡ fA .fst a
  H a = cong (fA .fst) (deck-homotopy a)

  -- The actual vertex components, including the chart-change paths.
  H-L : (z : Bool)
    → H (L z) ≡ cong (fA .fst) (δ-L z ∙ half-L z)
  H-L z = cong (cong (fA .fst))
    (transportRefl _ ∙ transportRefl (δ-L z ∙ half-L z))

  H-R : (z : Bool)
    → H (Rv z) ≡ cong (fA .fst) (δ-R z ∙ half-R z)
  H-R z = cong (cong (fA .fst))
    (transportRefl _ ∙ transportRefl (δ-R z ∙ half-R z))
