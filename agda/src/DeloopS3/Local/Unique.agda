{-# OPTIONS --cubical --safe #-}
-- Uniqueness and the mapping-space universal property of localization
-- at an arbitrary family of maps. The induction uses path families into a
-- local target, not a general dependent eliminator: local types need not
-- be closed under dependent sums.
module DeloopS3.Local.Unique where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivCong)
open import Cubical.Foundations.Equiv.PathSplit using (toIsEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Localization.Base
open import Cubical.HITs.Localization.Properties using (rec)

-- applying an equivalence to squares is an equivalence on squares
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) where
  private
    φ = equivFun e

  sqMap : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
          {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        → Square a₀₋ a₁₋ a₋₀ a₋₁ → Square (cong φ a₀₋) (cong φ a₁₋) (cong φ a₋₀) (cong φ a₋₁)
  sqMap K i j = φ (K i j)

  isEquivSq : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
              {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
            → isEquiv (sqMap {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁})
  isEquivSq {a₀₀} {a₀₁} {a₀₋} {a₁₀} {a₁₁} {a₁₋} {a₋₀} {a₋₁} =
    J (λ a₁₀ a₋₀ → {a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
                 → isEquiv (sqMap {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}))
      (λ {a₁₁} {a₁₋} {a₋₁} →
        J (λ a₁₁ a₋₁ → {a₁₋ : a₀₀ ≡ a₁₁}
                     → isEquiv (sqMap {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = refl} {a₋₁ = a₋₁}))
          (λ {a₁₋} → isEquivCong {x = a₀₋} {y = a₁₋} ((λ p → cong φ p) , isEquivCong e)) a₋₁)
      a₋₀

module Unique {ℓα ℓs ℓt} {A : Type ℓα} {S : A → Type ℓs} {T : A → Type ℓt}
              {F : ∀ α → S α → T α} {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
              (lY : isLocal F Y) where

  preE : ∀ α → (T α → Y) ≃ (S α → Y)
  preE α = (λ g → g ∘ F α) , toIsEquiv _ (lY α)

  ---- level 1: families of paths over T α

  module _ (α : A) (a b : T α → Y) (w : (s : S α) → a (F α s) ≡ b (F α s)) where
    private
      cE : (a ≡ b) ≃ ((a ∘ F α) ≡ (b ∘ F α))
      cE = _ , isEquivCong (preE α)

    ext1 : (t : T α) → a t ≡ b t
    ext1 = funExt⁻ (invEq cE (funExt w))

    ext1-β : (λ s → ext1 (F α s)) ≡ w
    ext1-β = cong funExt⁻ (secEq cE (funExt w))

  ---- level 2: families of squares over T α

  module _ (α : A) {c₀₀ c₀₁ c₁₀ c₁₁ : T α → Y}
           (s₀₋ : (t : T α) → c₀₀ t ≡ c₀₁ t) (s₁₋ : (t : T α) → c₁₀ t ≡ c₁₁ t)
           (s₋₀ : (t : T α) → c₀₀ t ≡ c₁₀ t) (s₋₁ : (t : T α) → c₀₁ t ≡ c₁₁ t)
           (W : (s : S α) → Square (s₀₋ (F α s)) (s₁₋ (F α s)) (s₋₀ (F α s)) (s₋₁ (F α s))) where
    private
      sE : Square {A = T α → Y} (λ j t → s₀₋ t j) (λ j t → s₁₋ t j) (λ i t → s₋₀ t i) (λ i t → s₋₁ t i)
         ≃ Square {A = S α → Y} (λ j s → s₀₋ (F α s) j) (λ j s → s₁₋ (F α s) j)
                  (λ i s → s₋₀ (F α s) i) (λ i s → s₋₁ (F α s) i)
      sE = _ , isEquivSq (preE α)
      W' : Square {A = S α → Y} (λ j s → s₀₋ (F α s) j) (λ j s → s₁₋ (F α s) j)
                  (λ i s → s₋₀ (F α s) i) (λ i s → s₋₁ (F α s) i)
      W' i j s = W s i j

    ext2 : (t : T α) → Square (s₀₋ t) (s₁₋ t) (s₋₀ t) (s₋₁ t)
    ext2 t i j = invEq sE W' i j t

    ext2-β : (λ s → ext2 (F α s)) ≡ W
    ext2-β k s i j = secEq sE W' k i j s

  -- Induct into x ↦ f x ≡ g x. Inverse precomposition handles ext and
  -- ≡ext on paths and squares; its section laws, with transport fillers,
  -- handle the coherence constructors isExt and ≡isExt.
  ---- the induction

  module _ (f g : Localize F X → Y) (H : (x : X) → f ∣ x ∣ ≡ g ∣ x ∣) where

    private
      -- level-1 transport back along isExt
      Q1 : ∀ α φ s → I → Type ℓ'
      Q1 α φ s k = f (isExt α φ s k) ≡ g (isExt α φ s k)

      w1 : ∀ α φ → ((s : S α) → f (φ s) ≡ g (φ s))
         → (s : S α) → f (ext α φ (F α s)) ≡ g (ext α φ (F α s))
      w1 α φ u s = transport (λ k → Q1 α φ s (~ k)) (u s)

      w1-fill : ∀ α φ (u : (s : S α) → f (φ s) ≡ g (φ s)) (s : S α)
              → PathP (Q1 α φ s) (w1 α φ u s) (u s)
      w1-fill α φ u s = symP (transport-filler (λ k → Q1 α φ s (~ k)) (u s))

      -- level-2 transport back along ≡isExt
      module _ α (g' h' : T α → Localize F X) (p : (s : S α) → g' (F α s) ≡ h' (F α s))
               (u₀ : (t : T α) → f (g' t) ≡ g (g' t)) (u₁ : (t : T α) → f (h' t) ≡ g (h' t)) where
        Q2 : (s : S α) → I → Type ℓ'
        Q2 s k = Square (u₀ (F α s)) (u₁ (F α s))
                        (λ i → f (≡isExt α g' h' p s k i)) (λ i → g (≡isExt α g' h' p s k i))

        w2 : ((s : S α) → Q2 s i1) → (s : S α) → Q2 s i0
        w2 V s = transport (λ k → Q2 s (~ k)) (V s)

        w2-fill : (V : (s : S α) → Q2 s i1) (s : S α) → PathP (Q2 s) (w2 V s) (V s)
        w2-fill V s = symP (transport-filler (λ k → Q2 s (~ k)) (V s))

    ≡onη : (x : Localize F X) → f x ≡ g x
    ≡onη ∣ x ∣ = H x
    ≡onη (ext α φ t) =
      ext1 α (f ∘ ext α φ) (g ∘ ext α φ) (w1 α φ (λ s → ≡onη (φ s))) t
    ≡onη (isExt α φ s i) =
      ((λ k → ext1-β α (f ∘ ext α φ) (g ∘ ext α φ) (w1 α φ (λ s → ≡onη (φ s))) k s)
        ◁ w1-fill α φ (λ s → ≡onη (φ s)) s) i
    ≡onη (≡ext α g' h' p t i) =
      ext2 α (λ t → ≡onη (g' t)) (λ t → ≡onη (h' t))
             (λ t i → f (≡ext α g' h' p t i)) (λ t i → g (≡ext α g' h' p t i))
             (w2 α g' h' p (λ t → ≡onη (g' t)) (λ t → ≡onη (h' t))
                 (λ s i j → ≡onη (p s i) j)) t i
    ≡onη (≡isExt α g' h' p s k i) =
      ((λ m → ext2-β α (λ t → ≡onη (g' t)) (λ t → ≡onη (h' t))
                 (λ t i → f (≡ext α g' h' p t i)) (λ t i → g (≡ext α g' h' p t i))
                 (w2 α g' h' p (λ t → ≡onη (g' t)) (λ t → ≡onη (h' t))
                     (λ s i j → ≡onη (p s i) j)) m s)
        ◁ w2-fill α g' h' p (λ t → ≡onη (g' t)) (λ t → ≡onη (h' t))
                  (λ s i j → ≡onη (p s i) j) s) k i

    unique : f ≡ g
    unique = funExt ≡onη

  -- the full universal property: precomposition with ∣_∣ is an equivalence
  isEquiv-preη : isEquiv (λ (f : Localize F X → Y) → f ∘ ∣_∣)
  isEquiv-preη = isoToIsEquiv (iso (λ f → f ∘ ∣_∣) (rec lY) (λ _ → refl)
                                   (λ f → unique (rec lY (f ∘ ∣_∣)) f (λ _ → refl)))
