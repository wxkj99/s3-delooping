{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.PullbackFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws using (lUnit ; rUnit)
open import Cubical.Foundations.Path using (flipSquareEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd)
open import DeloopS3.Local.Fracture.Fracture.Maps using (PB)

private
  J-right : {A : Type} {y : A}
    (P : (x : A) → x ≡ y → Type) → P y refl
    → {x : A} (p : x ≡ y) → P x p
  J-right P d p = J (λ x q → P x (sym q)) d (sym p)

  whisker-type : {A : Type} {a₀ a₁ b₀ b₁ c₀ c₁ : A}
    (h₀ : a₀ ≡ b₀) (h₁ : a₁ ≡ b₁)
    (q₀ : b₀ ≡ c₀) (q₁ : b₁ ≡ c₁)
    (s : c₀ ≡ c₁) (p : a₀ ≡ a₁) → Type
  whisker-type h₀ h₁ q₀ q₁ s p =
    Square (sym h₀ ∙ p ∙ h₁) s q₀ q₁
      ≃ Square (h₀ ∙ q₀) (h₁ ∙ q₁ ∙ sym s) p refl

  erase-units : {A : Type} {x y : A} (p : x ≡ y)
    → refl ∙ p ∙ refl ≡ p
  erase-units p = sym (lUnit (p ∙ refl)) ∙ sym (rUnit p)

  unit₂ : {A : Type} {x : A} → refl {x = x} ∙ refl ≡ refl
  unit₂ = sym (lUnit refl)

  unit₃ : {A : Type} {x : A} → refl {x = x} ∙ refl ∙ refl ≡ refl
  unit₃ = sym (lUnit (refl ∙ refl)) ∙ unit₂

  whisker-base : {A : Type} {x : A} (p : x ≡ x)
    → whisker-type refl refl refl refl refl p
  whisker-base p = compEquiv
    (pathToEquiv (λ i → Square (erase-units p i) refl refl refl))
    (compEquiv flipSquareEquiv
      (invEquiv (pathToEquiv (λ i → Square (unit₂ i) (unit₃ i) p refl))))

  whisker-h₁ : {A : Type} {x a₁ : A} (h₁ : a₁ ≡ x) (p : x ≡ a₁)
    → whisker-type refl h₁ refl refl refl p
  whisker-h₁ {x = x} h₁ = J-right
    (λ a₁ h₁ → (p : x ≡ a₁) → whisker-type refl h₁ refl refl refl p)
    whisker-base h₁

  whisker-q₁ : {A : Type} {x b₁ : A} (q₁ : b₁ ≡ x)
    → {a₁ : A} (h₁ : a₁ ≡ b₁) (p : x ≡ a₁)
    → whisker-type refl h₁ refl q₁ refl p
  whisker-q₁ {A} {x} q₁ = J-right
    (λ b₁ q₁ → {a₁ : A} (h₁ : a₁ ≡ b₁) (p : x ≡ a₁)
      → whisker-type refl h₁ refl q₁ refl p)
    whisker-h₁ q₁

  whisker-s : {A : Type} {x c₁ : A} (s : x ≡ c₁)
    → {b₁ a₁ : A} (q₁ : b₁ ≡ c₁) (h₁ : a₁ ≡ b₁) (p : x ≡ a₁)
    → whisker-type refl h₁ refl q₁ s p
  whisker-s {A} {x} s = J
    (λ c₁ s → {b₁ a₁ : A} (q₁ : b₁ ≡ c₁) (h₁ : a₁ ≡ b₁) (p : x ≡ a₁)
      → whisker-type refl h₁ refl q₁ s p)
    (λ q₁ h₁ p → whisker-q₁ q₁ h₁ p) s

  whisker-q₀ : {A : Type} {x c₀ : A} (q₀ : x ≡ c₀)
    → {c₁ b₁ a₁ : A} (s : c₀ ≡ c₁) (q₁ : b₁ ≡ c₁)
    (h₁ : a₁ ≡ b₁) (p : x ≡ a₁)
    → whisker-type refl h₁ q₀ q₁ s p
  whisker-q₀ {A} {x} q₀ = J
    (λ c₀ q₀ → {c₁ b₁ a₁ : A} (s : c₀ ≡ c₁) (q₁ : b₁ ≡ c₁)
      (h₁ : a₁ ≡ b₁) (p : x ≡ a₁) → whisker-type refl h₁ q₀ q₁ s p)
    (λ s q₁ h₁ p → whisker-s s q₁ h₁ p) q₀

square-whisker-equiv : {A : Type} {a₀ a₁ b₀ b₁ c₀ c₁ : A}
  (h₀ : a₀ ≡ b₀) (h₁ : a₁ ≡ b₁)
  (q₀ : b₀ ≡ c₀) (q₁ : b₁ ≡ c₁)
  (s : c₀ ≡ c₁) (p : a₀ ≡ a₁)
  → Square (sym h₀ ∙ p ∙ h₁) s q₀ q₁
      ≃ Square (h₀ ∙ q₀) (h₁ ∙ q₁ ∙ sym s) p refl
square-whisker-equiv {A} {a₀} h₀ h₁ q₀ q₁ s p =
  J (λ b₀ h₀ → {c₀ c₁ b₁ a₁ : A} (q₀ : b₀ ≡ c₀)
      (s : c₀ ≡ c₁) (q₁ : b₁ ≡ c₁) (h₁ : a₁ ≡ b₁) (p : a₀ ≡ a₁)
      → whisker-type h₀ h₁ q₀ q₁ s p)
    (λ q₀ s q₁ h₁ p → whisker-q₀ q₀ s q₁ h₁ p) h₀ q₀ s q₁ h₁ p

module Cospan
  (E₀ E₁ E* B₀ B₁ B* : Type)
  (p₀ : E₀ → B₀) (p₁ : E₁ → B₁) (p* : E* → B*)
  (v₀ : E₀ → E*) (v₁ : E₁ → E*)
  (u₀ : B₀ → B*) (u₁ : B₁ → B*)
  (H₀ : (x : E₀) → p* (v₀ x) ≡ u₀ (p₀ x))
  (H₁ : (y : E₁) → p* (v₁ y) ≡ u₁ (p₁ y)) where

  pT : PB v₀ v₁ → PB u₀ u₁
  pT (x , y , r) = p₀ x , p₁ y , sym (H₀ x) ∙ cong p* r ∙ H₁ y

  module At (b₀ : B₀) (b₁ : B₁) (s : u₀ b₀ ≡ u₁ b₁) where
    X₀ = fiber p₀ b₀
    X₁ = fiber p₁ b₁
    X* = fiber p* (u₀ b₀)

    a : X₀ → X*
    a (x , q) = v₀ x , H₀ x ∙ cong u₀ q

    b : X₁ → X*
    b (y , q) = v₁ y , H₁ y ∙ cong u₁ q ∙ sym s

    private
      Code : Type
      Code = Σ[ x ∈ E₀ ] Σ[ q₀ ∈ p₀ x ≡ b₀ ]
        Σ[ y ∈ E₁ ] Σ[ q₁ ∈ p₁ y ≡ b₁ ] Σ[ r ∈ v₀ x ≡ v₁ y ]
        Square (sym (H₀ x) ∙ cong p* r ∙ H₁ y) s (cong u₀ q₀) (cong u₁ q₁)

      Code' : Type
      Code' = Σ[ x ∈ E₀ ] Σ[ q₀ ∈ p₀ x ≡ b₀ ]
        Σ[ y ∈ E₁ ] Σ[ q₁ ∈ p₁ y ≡ b₁ ] Σ[ r ∈ v₀ x ≡ v₁ y ]
        Square (H₀ x ∙ cong u₀ q₀) (H₁ y ∙ cong u₁ q₁ ∙ sym s) (cong p* r) refl

      fiber-code : Iso (fiber pT (b₀ , b₁ , s)) Code
      Iso.fun fiber-code ((x , y , r) , t) =
        x , (λ i → fst (t i)) , y , (λ i → fst (snd (t i))) , r ,
        (λ i → snd (snd (t i)))
      Iso.inv fiber-code (x , q₀ , y , q₁ , r , sq) =
        (x , y , r) , (λ i → q₀ i , q₁ i , sq i)
      Iso.sec fiber-code _ = refl
      Iso.ret fiber-code _ = refl

      code-equiv : Code ≃ Code'
      code-equiv = Σ-cong-equiv-snd λ x → Σ-cong-equiv-snd λ q₀ →
        Σ-cong-equiv-snd λ y → Σ-cong-equiv-snd λ q₁ →
        Σ-cong-equiv-snd λ r →
          square-whisker-equiv (H₀ x) (H₁ y) (cong u₀ q₀) (cong u₁ q₁) s (cong p* r)

      code-pullback : Iso Code' (PB a b)
      Iso.fun code-pullback (x , q₀ , y , q₁ , r , sq) =
        (x , q₀) , (y , q₁) , (λ i → r i , sq i)
      Iso.inv code-pullback ((x , q₀) , (y , q₁) , t) =
        x , q₀ , y , q₁ , (λ i → fst (t i)) , (λ i → snd (t i))
      Iso.sec code-pullback _ = refl
      Iso.ret code-pullback _ = refl

    fiber-equiv : fiber pT (b₀ , b₁ , s) ≃ PB a b
    fiber-equiv = compEquiv (isoToEquiv fiber-code)
      (compEquiv code-equiv (isoToEquiv code-pullback))

    first-projection : (w : fiber pT (b₀ , b₁ , s))
      → fst (equivFun fiber-equiv w)
        ≡ (fst (fst w) , cong fst (snd w))
    first-projection w = refl

    second-projection : (w : fiber pT (b₀ , b₁ , s))
      → fst (snd (equivFun fiber-equiv w))
        ≡ (fst (snd (fst w)) , cong (λ z → fst (snd z)) (snd w))
    second-projection w = refl
