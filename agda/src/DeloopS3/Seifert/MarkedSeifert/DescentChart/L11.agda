{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Fibre conjugation, vertical factorization and odd squares, with pointings retained.
module DeloopS3.Seifert.MarkedSeifert.DescentChart.L11 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Loopspace using (Ω→)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase)
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Base
  using (R; A; w₁; pr₁; δ; Ksign)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
  using (based; based-refl; based-comp; based-square)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (cong-based)
open import DeloopS3.Seifert.MarkedSeifert.DescentChart

-- No concrete descended family occurs in these path-algebra proofs.
opaque
  include-Ω : ∀ {ℓ ℓ′ ℓ″} {X : Pointed ℓ} {Y : Pointed ℓ′}
    {T : Type ℓ″} (f : X →∙ Y) (inc : Y .fst → T)
    (p : X .snd ≡ X .snd)
    → based (cong inc (f .snd)) (cong (inc ∘ f .fst) p)
      ≡ cong inc (Ω→ f .fst p)
  include-Ω f inc p = sym (cong-based inc (f .snd) (cong (f .fst) p))
    ∙ cong (cong inc) (sym (Ω-based f p))

  include-inverse-op : {X Y : Pointed ℓ-zero} {T : Type₀}
    (e d : X ≃∙ Y) (inc : X .fst → T)
    (eq : (p : Y .snd ≡ Y .snd)
      → Ω→ (≃∙map (invEquiv∙ e)) .fst p
        ≡ Ω→ (≃∙map (invEquiv∙ d)) .fst (sym p))
    (p : Y .snd ≡ Y .snd)
    → based (cong inc (invEquiv∙ e .snd)) (cong (inc ∘ invEq (e .fst)) p)
      ≡ based (cong inc (invEquiv∙ d .snd)) (cong (inc ∘ invEq (d .fst)) (sym p))
  include-inverse-op e d inc eq p = include-Ω (≃∙map (invEquiv∙ e)) inc p
    ∙ cong (cong inc) (eq p)
    ∙ sym (include-Ω (≃∙map (invEquiv∙ d)) inc (sym p))

  -- Move an equality of loops at the common pointing endpoint back
  -- to a square along the connecting edge v · u⁻¹.
  pointing-edge : ∀ {ℓ} {X : Type ℓ} {x y z : X}
    (u : x ≡ z) (v : y ≡ z) (m : y ≡ y) (n : x ≡ x)
    → based v m ≡ based u n
    → m ∙ (v ∙ sym u) ≡ (v ∙ sym u) ∙ n
  pointing-edge u v m n eq = Square→compPath
    (based-square (v ∙ sym u) m n
      (based-chain v (sym u) m
        ∙ cong (based (sym u)) eq ∙ based-inverse u n))

  commute-chain : ∀ {ℓ} {X : Type ℓ} {x y z : X}
    (w : x ≡ y) (c : y ≡ z) (l : x ≡ x) (m : y ≡ y) (n : z ≡ z)
    → l ∙ w ≡ w ∙ m → m ∙ c ≡ c ∙ n
    → l ∙ (w ∙ c) ≡ (w ∙ c) ∙ n
  commute-chain w c l m n e f = assoc l w c
    ∙ cong (_∙ c) e ∙ sym (assoc w m c)
    ∙ cong (w ∙_) f ∙ assoc w c n

  glue-conjugation : ∀ {ℓ} {X : Type ℓ} {x y z : X}
    (w : x ≡ y) (u : x ≡ z) (v : y ≡ z) (b : z ≡ z)
    (l : x ≡ x) (m : y ≡ y) (n : x ≡ x)
    → w ∙ v ≡ u ∙ b
    → l ∙ w ≡ w ∙ m
    → based v m ≡ based u n
    → l ∙ ((u ∙ b) ∙ sym u) ≡ ((u ∙ b) ∙ sym u) ∙ n
  glue-conjugation w u v b l m n eq nat op =
    cong (l ∙_) (sym word)
    ∙ commute-chain w (v ∙ sym u) l m n nat (pointing-edge u v m n op)
    ∙ cong (_∙ n) word
    where
    word : w ∙ (v ∙ sym u) ≡ (u ∙ b) ∙ sym u
    word = assoc w v (sym u) ∙ cong (_∙ sym u) eq

  -- The Sigma-path argument is untruncated; the fibre equivalence
  -- supplies an actual preimage of the vertical loop.
  factor-over : ∀ {ℓX ℓP ℓY} {X : Type ℓX} (P : X → Type ℓP)
    {Y : Type ℓY} (y : Y) (x : X) (e : Y ≃ P x)
    (k l : Path (Σ X P) (x , e .fst y) (x , e .fst y))
    → cong fst l ≡ cong fst k
    → Σ[ p ∈ (y ≡ y) ] (l ≡ cong (λ t → x , e .fst t) p ∙ k)
  factor-over P y x e k l eq = p ,
    sym (compPathr-cancel k l) ∙ cong (_∙ k) vertical
    where
    v : Path (Σ _ P) (x , e .fst y) (x , e .fst y)
    v = l ∙ sym k
    projects : cong fst v ≡ refl
    projects = cong-∙ fst l (sym k)
      ∙ cong (_∙ sym (cong fst k)) eq ∙ rCancel (cong fst k)
    fibre : Σ[ r ∈ (e .fst y ≡ e .fst y) ]
      (v ≡ cong (λ t → x , t) r)
    fibre = vertical-path {P = P} {u = x , e .fst y} v projects
    p : y ≡ y
    p = invEq (congEquiv e) (fibre .fst)
    vertical : v ≡ cong (λ t → x , e .fst t) p
    vertical = fibre .snd
      ∙ cong (cong (λ t → x , t)) (sym (secEq (congEquiv e) (fibre .fst)))

  square-word : ∀ {ℓ} {X : Type ℓ} {x : X} (v k : x ≡ x)
    → k ∙ v ≡ sym v ∙ k
    → (v ∙ k) ∙ (v ∙ k) ≡ k ∙ k
  square-word v k eq = sym (assoc v k (v ∙ k))
    ∙ cong (v ∙_) (assoc k v k)
    ∙ cong (λ t → v ∙ (t ∙ k)) eq
    ∙ cong (v ∙_) (sym (assoc (sym v) k k))
    ∙ compPathl-cancel v (k ∙ k)

opaque
  based-image-square : ∀ {ℓ ℓ′} {X : Type ℓ} {Y : Type ℓ′}
    (f : X → Y) {x : X} {y : Y} (b : f x ≡ y) (l : x ≡ x)
    → based b (cong f (l ∙ l))
      ≡ based b (cong f l) ∙ based b (cong f l)
  based-image-square f b l = cong (based b) (cong-∙ f l l)
    ∙ based-comp b (cong f l) (cong f l)

opaque
  op-loop : (a : A) (p : 0C ≡ 0C)
    → based (q (δ a)) (V (δ a) p) ≡ based (q a) (V a (sym p))
  op-loop (x , y) p = include-inverse-op
    {X = SignC (w₁ x) , embase} {Y = C , 0C} {T = Ksign}
    (ε∙ (w₁ x) (op (w₁ x) y)) (ε∙ (w₁ x) y)
    (λ t → x , t) (inverse-ε-op-loop (w₁ x) y) p

  fibre-conjugation : (a : A) (p : 0C ≡ 0C)
    → J₀ a ∙ V a p ≡ V a (sym p) ∙ J₀ a
  fibre-conjugation a p = sym (glue-conjugation
    {X = Ksign} {x = F₀ a} {y = F₀ (δ a)} {z = Z (pr₁ a)}
    (cong F₀ (sym (h a))) (q a) (q (δ a)) (cong Z (τ a))
    (V a (sym p)) (V (δ a) (sym p)) (V a p)
    (naturality q (sym (h a)))
    (sym (naturality (λ a → V a (sym p)) (sym (h a))))
    (op-loop a (sym p)))

  vertical-factor : (a : A) (l : F₀ a ≡ F₀ a) → cong fst l ≡ τ a
    → Σ[ p ∈ (0C ≡ 0C) ] (l ≡ V a p ∙ J₀ a)
  vertical-factor (x , y) l eq = factor-over
    {X = R} (SignC ∘ w₁) {Y = C} 0C x (invEquiv (ε (w₁ x) y))
    (J₀ (x , y)) l (eq ∙ sym (J-projects (x , y)))

  odd-square : (a : A) (l : F₀ a ≡ F₀ a) → cong fst l ≡ τ a
    → l ∙ l ≡ J₀ a ∙ J₀ a
  odd-square a l eq = cong (λ t → t ∙ t) (factor .snd)
    ∙ square-word (V a (factor .fst)) (J₀ a) (fibre-conjugation a (factor .fst))
    where
    factor : Σ[ p ∈ (0C ≡ 0C) ] (l ≡ V a p ∙ J₀ a)
    factor = vertical-factor a l eq
