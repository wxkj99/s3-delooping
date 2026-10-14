{-# OPTIONS --cubical --safe --lossy-unification #-}

module DeloopS3.Bridge.DegreeSpan.TotalWindowRealizationSquare where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.Path using (Square≃doubleComp)
open import Cubical.Foundations.GroupoidLaws
  using (assoc; rCancel; rUnit; symDistr; doubleCompPath-elim;
         doubleCompPath-elim')

abstract
  unwhisker-mark :
    {ℓ : Level} {A : Type ℓ} {a b c d e : A}
    (t : a ≡ b) (k : b ≡ c) (T : d ≡ e)
    (p : a ≡ d) (H : b ≡ e)
    (mark : Square p H t T)
    → ((sym k ∙ H) ∙ sym T) ≡ (sym (t ∙ k) ∙ p)
  unwhisker-mark t k T p H mark =
    ((sym k ∙ H) ∙ sym T)
      ≡⟨ cong (λ h′ → (sym k ∙ h′) ∙ sym T) (sym rel) ⟩
    ((sym k ∙ (sym t ∙∙ p ∙∙ T)) ∙ sym T)
      ≡⟨ cong (λ h′ → (sym k ∙ h′) ∙ sym T)
           (doubleCompPath-elim (sym t) p T) ⟩
    ((sym k ∙ ((sym t ∙ p) ∙ T)) ∙ sym T)
      ≡⟨ cong (_∙ sym T) (assoc (sym k) (sym t ∙ p) T) ⟩
    (((sym k ∙ (sym t ∙ p)) ∙ T) ∙ sym T)
      ≡⟨ sym (assoc (sym k ∙ (sym t ∙ p)) T (sym T)) ⟩
    ((sym k ∙ (sym t ∙ p)) ∙ (T ∙ sym T))
      ≡⟨ cong ((sym k ∙ (sym t ∙ p)) ∙_) (rCancel T) ⟩
    ((sym k ∙ (sym t ∙ p)) ∙ refl)
      ≡⟨ sym (rUnit (sym k ∙ (sym t ∙ p))) ⟩
    (sym k ∙ (sym t ∙ p))
      ≡⟨ assoc (sym k) (sym t) p ⟩
    ((sym k ∙ sym t) ∙ p)
      ≡⟨ cong (_∙ p) (sym (symDistr t k)) ⟩
    (sym (t ∙ k) ∙ p) ∎
    where
    rel : (sym t ∙∙ p ∙∙ T) ≡ H
    rel = equivFun (Square≃doubleComp p H t T) mark

  marked-leg-square :
    {ℓ : Level} {A : Type ℓ} {a b c d e f g j : A}
    (t : a ≡ b) (k : b ≡ c) (T : d ≡ e) (H : b ≡ e)
    (alpha : a ≡ f) (beta : c ≡ g) (s : f ≡ g)
    (h : f ≡ j) (r : d ≡ j)
    (mark : Square (alpha ∙∙ h ∙∙ sym r) H t T)
    (approx : Square (t ∙ k) s alpha beta)
    → Square ((sym k ∙ H) ∙ sym T) (sym s ∙ h) beta r
  marked-leg-square {a = a} {d = d}
    t k T H alpha beta s h r mark approx =
    unwhisker-mark t k T p H mark ◁
      (inverse-approx ∙₂ delete-whiskers)
    where
    p : a ≡ d
    p = alpha ∙∙ h ∙∙ sym r

    inverse-approx : Square (sym (t ∙ k)) (sym s) beta alpha
    inverse-approx q i = approx q (~ i)

    delete-whiskers : Square p h alpha r
    delete-whiskers q i = doubleCompPath-filler alpha h (sym r) (~ q) i

  nested-seam :
    {ℓ : Level} {A : Type ℓ} {x0 x1 x2 y0 y1 y2 : A}
    (a : x0 ≡ x1) (b : x1 ≡ x2) (p : x2 ≡ y2)
    (c : y0 ≡ y1) (d : y1 ≡ y2)
    → (a ∙∙ (b ∙∙ p ∙∙ sym d) ∙∙ sym c)
      ≡ ((a ∙ b) ∙∙ p ∙∙ sym (c ∙ d))
  nested-seam a b p c d =
    (a ∙∙ (b ∙∙ p ∙∙ sym d) ∙∙ sym c)
      ≡⟨ doubleCompPath-elim' a (b ∙∙ p ∙∙ sym d) (sym c) ⟩
    (a ∙ ((b ∙∙ p ∙∙ sym d) ∙ sym c))
      ≡⟨ cong (λ q → a ∙ (q ∙ sym c))
           (doubleCompPath-elim' b p (sym d)) ⟩
    (a ∙ ((b ∙ (p ∙ sym d)) ∙ sym c))
      ≡⟨ cong (a ∙_) (sym (assoc b (p ∙ sym d) (sym c))) ⟩
    (a ∙ (b ∙ ((p ∙ sym d) ∙ sym c)))
      ≡⟨ assoc a b ((p ∙ sym d) ∙ sym c) ⟩
    ((a ∙ b) ∙ ((p ∙ sym d) ∙ sym c))
      ≡⟨ cong ((a ∙ b) ∙_) (sym (assoc p (sym d) (sym c))) ⟩
    ((a ∙ b) ∙ (p ∙ (sym d ∙ sym c)))
      ≡⟨ cong (λ q → (a ∙ b) ∙ (p ∙ q)) (sym (symDistr c d)) ⟩
    ((a ∙ b) ∙ (p ∙ sym (c ∙ d)))
      ≡⟨ sym (doubleCompPath-elim' (a ∙ b) p (sym (c ∙ d))) ⟩
    ((a ∙ b) ∙∙ p ∙∙ sym (c ∙ d)) ∎
