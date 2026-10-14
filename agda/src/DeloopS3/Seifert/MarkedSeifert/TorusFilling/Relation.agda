{-# OPTIONS --safe --cubical #-}

-- The torus-filling relation type is untruncated.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.Relation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
import DeloopS3.Seifert.MarkedSeifert.WInterface as W

module Normalize {ℓ : Level} {X : Type ℓ} {a : X} (j r : a ≡ a) where
  L : (a ≡ a) → (a ≡ a)
  L p = (sym j ∙ p) ∙ r

  abstract
    LEquiv : (a ≡ a) ≃ (a ≡ a)
    LEquiv = compEquiv
      (compPathlEquiv {A = X} {x = a} {y = a} {z = a} (sym j))
      (compPathrEquiv {A = X} {x = a} {y = a} {z = a} r)

    LEquiv-map : LEquiv .fst ≡ L
    LEquiv-map = refl

  endpoint₀ : L (j ∙ j) ≡ j ∙ r
  endpoint₀ = cong (_∙ r)
    (assoc (sym j) j j ∙ cong (_∙ j) (lCancel j) ∙ sym (lUnit j))

  endpoint₁ : L ((j ∙ sym r) ∙ (j ∙ sym r)) ≡ sym r ∙ j
  endpoint₁ =
    cong (_∙ r)
      (assoc (sym j) (j ∙ sym r) (j ∙ sym r)
        ∙ cong (_∙ (j ∙ sym r))
          (assoc (sym j) j (sym r)
            ∙ cong (_∙ sym r) (lCancel j) ∙ sym (lUnit (sym r))))
    ∙ sym (assoc (sym r) (j ∙ sym r) r)
    ∙ cong (sym r ∙_)
      (sym (assoc j (sym r) r)
        ∙ cong (j ∙_) (lCancel r) ∙ sym (rUnit j))

  forward : (j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r))
    → j ∙ r ≡ sym r ∙ j
  forward q = (sym endpoint₀ ∙ cong L q) ∙ endpoint₁

  -- Keep computational maps transparent, but not their equivalence proofs.
  backward : (j ∙ r ≡ sym r ∙ j)
    → j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r)
  backward = invEq (compEquiv
    (congEquiv {A = a ≡ a} {B = a ≡ a}
      {x = j ∙ j} {y = (j ∙ sym r) ∙ (j ∙ sym r)}
      (compEquiv (compPathlEquiv (sym j)) (compPathrEquiv r)))
    (compEquiv (compPathlEquiv (sym endpoint₀)) (compPathrEquiv endpoint₁)))

  abstract
    relationNielsen : (j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r))
      ≃ (j ∙ r ≡ sym r ∙ j)
    relationNielsen = compEquiv
      (congEquiv {A = a ≡ a} {B = a ≡ a}
        {x = j ∙ j} {y = (j ∙ sym r) ∙ (j ∙ sym r)}
        (compEquiv (compPathlEquiv (sym j)) (compPathrEquiv r)))
      (compEquiv (compPathlEquiv (sym endpoint₀)) (compPathrEquiv endpoint₁))

    forward-backward : (q : j ∙ r ≡ sym r ∙ j) → forward (backward q) ≡ q
    forward-backward = secEq relationNielsen

    backward-forward : (q : j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r))
      → backward (forward q) ≡ q
    backward-forward = retEq relationNielsen

abstract
  relationNielsen : {ℓ : Level} {X : Type ℓ} {a : X} (j r : a ≡ a)
    → (j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r)) ≃ (j ∙ r ≡ sym r ∙ j)
  relationNielsen = Normalize.relationNielsen

-- The complete Σ-data equivalence retains paths in the last coordinate.
abstract
  relationData : {ℓ : Level} (X : Type ℓ)
    → (Σ[ a ∈ X ] Σ[ j ∈ a ≡ a ] Σ[ r ∈ a ≡ a ]
        (j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r)))
      ≃ (Σ[ a ∈ X ] Σ[ j ∈ a ≡ a ] Σ[ r ∈ a ≡ a ]
        (j ∙ r ≡ sym r ∙ j))
  relationData X = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ j →
    Σ-cong-equiv-snd λ r → Normalize.relationNielsen {X = X} {a = a} j r

-- The normalized, still untruncated, relation HIT.
data KleinRel : Type₀ where
  vertex : KleinRel
  j r : vertex ≡ vertex
  κ : j ∙ r ≡ sym r ∙ j

normalizeHIT : W.RelJR → KleinRel
normalizeHIT W.vertex = vertex
normalizeHIT (W.j i) = j i
normalizeHIT (W.r i) = r i
normalizeHIT (W.relation i k) = Normalize.backward j r κ i k

denormalizeHIT : KleinRel → W.RelJR
denormalizeHIT vertex = W.vertex
denormalizeHIT (j i) = W.j i
denormalizeHIT (r i) = W.r i
denormalizeHIT (κ i k) = Normalize.forward W.j W.r W.relation i k

abstract
  normalize-section : (z : KleinRel) → normalizeHIT (denormalizeHIT z) ≡ z
  normalize-section vertex = refl
  normalize-section (j i) = refl
  normalize-section (r i) = refl
  normalize-section (κ i k) l = cube i k l
    where
    cube : Cube ((λ i k → j i) ∙v' (λ i k → r i))
      ((λ i k → r (~ i)) ∙v' (λ i k → j i))
      (λ i k → vertex) (λ i k → vertex)
      (λ i k → normalizeHIT (denormalizeHIT (κ i k))) κ
    cube = sym (∙v≡∙v' (λ i k → j i) (λ i k → r i)) ◁
      (λ i k l → Normalize.forward-backward j r κ l i k)
      ▷ ∙v≡∙v' (λ i k → r (~ i)) (λ i k → j i)

  normalize-retraction : (z : W.RelJR) → denormalizeHIT (normalizeHIT z) ≡ z
  normalize-retraction W.vertex = refl
  normalize-retraction (W.j i) = refl
  normalize-retraction (W.r i) = refl
  normalize-retraction (W.relation i k) l = cube i k l
    where
    jsq : Square {A = W.RelJR} refl refl W.j W.j
    jsq i k = W.j i

    jr-square : Square {A = W.RelJR} refl refl (W.j ∙ sym W.r) (W.j ∙ sym W.r)
    jr-square = (λ i k → W.j i) ∙v' (λ i k → W.r (~ i))

    right-face : (λ i k → ((W.j ∙ sym W.r) ∙ (W.j ∙ sym W.r)) i)
      ≡ jr-square ∙v' jr-square
    right-face = ∙v≡∙v' (λ i k → (W.j ∙ sym W.r) i)
      (λ i k → (W.j ∙ sym W.r) i)
      ∙ cong₂ _∙v'_ (∙v≡∙v' (λ i k → W.j i) (λ i k → W.r (~ i)))
        (∙v≡∙v' (λ i k → W.j i) (λ i k → W.r (~ i)))

    cube : Cube (jsq ∙v' jsq) (jr-square ∙v' jr-square)
      (λ i k → W.vertex) (λ i k → W.vertex)
      (λ i k → denormalizeHIT (normalizeHIT (W.relation i k))) W.relation
    cube = sym (∙v≡∙v' jsq jsq) ◁
      (λ i k l → Normalize.backward-forward W.j W.r W.relation l i k)
      ▷ right-face

  RelJR≃KleinRel : W.RelJR ≃ KleinRel
  RelJR≃KleinRel = isoToEquiv
    (iso normalizeHIT denormalizeHIT normalize-section normalize-retraction)

  RelJR≃KleinRel-map : RelJR≃KleinRel .fst ≡ normalizeHIT
  RelJR≃KleinRel-map = refl

  normalize-base : normalizeHIT W.vertex ≡ vertex
  normalize-base = refl

  normalize-j : cong normalizeHIT W.j ≡ j
  normalize-j = refl

  normalize-r : cong normalizeHIT W.r ≡ r
  normalize-r = refl
