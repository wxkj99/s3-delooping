{-# OPTIONS --safe --cubical #-}

-- Generic path algebra for marked identity-leg cancellation.
-- Keeping these lemmas generic prevents normalization of the EM models.
module DeloopS3.Move.CancelMinimalCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Pushout.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    X : Type ℓ
    Y : Type ℓ'
    B : Type ℓ''

-- An actual equivalence in the slice, including its map homotopy.
EquivOver : {X : Type ℓ} {Y : Type ℓ'} {B : Type ℓ''}
  → (X → B) → (Y → B) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
EquivOver {X = X} {Y = Y} m n = Σ[ e ∈ (X ≃ Y) ] ((x : X) → m x ≡ n (e .fst x))

transportMarking : (e : X ≃ Y) (m : X → B)
  → Σ[ n ∈ (Y → B) ] EquivOver m n
transportMarking e m = (m ∘ invEq e) , e , λ x → cong m (sym (retEq e x))

Σ-over-equiv : (V : B → Type ℓ''') {m : X → B} {n : Y → B}
  → EquivOver m n → Σ X (V ∘ m) ≃ Σ Y (V ∘ n)
Σ-over-equiv V (e , η) = compEquiv
  (Σ-cong-equiv-snd (λ x → pathToEquiv (cong V (η x))))
  (Σ-cong-equiv-fst e)

-- Transport in the based path family is RIGHT concatenation.
transport-path-right : {B : Type ℓ} (b : B) {k l : B}
  (p : k ≡ l) (u : b ≡ k)
  → transport (cong (b ≡_) p) u ≡ u ∙ p
transport-path-right b {k} p = J
  (λ l p → (u : b ≡ k) → transport (cong (b ≡_) p) u ≡ u ∙ p)
  (λ u → transportRefl u ∙ rUnit u) p

-- Univalence turns the specified seam naturality into a path of
-- equivalences.  Its argument is a coherent function, not pointwise data
-- modulo truncation, so its higher-dimensional instances are retained.
ua-equiv-family : {A A' : Type ℓ} (e : A ≃ A')
  (B : I → Type ℓ') (f₀ : A ≃ B i0) (f₁ : A' ≃ B i1)
  (h : (a : A) → PathP B (f₀ .fst a) (f₁ .fst (e .fst a)))
  → PathP (λ i → ua e i ≃ B i) f₀ f₁
ua-equiv-family e B f₀ f₁ h i .fst = ua→ {e = e} {B = B} {f₀ = f₀ .fst} {f₁ = f₁ .fst} h i
ua-equiv-family e B f₀ f₁ h i .snd =
  isProp→PathP (λ i → isPropIsEquiv (ua→ {e = e} {B = B} {f₀ = f₀ .fst} {f₁ = f₁ .fst} h i)) (f₀ .snd) (f₁ .snd) i

-- The identity leg is the primitive loop--cell pair in
-- the minimal model.  These are untruncated pushouts.
module IdentityCancellation {A : Type ℓ} {R : Type ℓ'} (b : A → R) where
  E = Pushout (idfun A) b

  r : E → R
  r (inl a) = b a
  r (inr t) = t
  r (push a i) = b a

  j : R → E
  j = inr

  rj : (t : R) → r (j t) ≡ t
  rj t = refl

  jr : (z : E) → j (r z) ≡ z
  jr (inl a) = sym (push a)
  jr (inr t) = refl
  jr (push a i) k = push a (i ∨ ~ k)

  cancel : E ≃ R
  cancel = isoToEquiv (iso r j rj jr)

module PrimitiveLoopCell {C : Type ℓ} {B : Type ℓ'}
  (b₀ : B) (α : C → b₀ ≡ b₀) where

  O : Type ℓ
  O = Pushout (idfun C) (λ _ → tt)

  v : O
  v = inr tt

  c : O → B
  c (inl a) = b₀
  c (inr tt) = b₀
  c (push a i) = α a i

  -- The four-boundary contraction square.
  h : (z : O) → z ≡ v
  h (inl a) = push a
  h (inr tt) = refl
  h (push a i) j = push a (i ∨ j)

  qEquiv : O ≃ Unit
  qEquiv = isoToEquiv (iso (λ _ → tt) (λ _ → v)
    (λ _ → refl) (λ z → sym (h z)))

  η : (z : O) → c z ≡ b₀
  η z = cong c (h z)

  primitive-loop-cell-cancel : EquivOver c (λ (_ : Unit) → b₀)
  primitive-loop-cell-cancel = qEquiv , η

  η-graph : (a : C) → η (inl a) ≡ α a
  η-graph a = refl

  η-cap : η (inr tt) ≡ refl
  η-cap = refl

  η-seam : (a : C) (i j : I) → η (push a i) j ≡ α a (i ∨ j)
  η-seam a i j = refl
