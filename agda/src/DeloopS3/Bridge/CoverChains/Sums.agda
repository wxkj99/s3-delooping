{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.Sums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
import Cubical.Data.Fin as F
import Cubical.Data.SumFin as SF
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (yes; no; ¬_)
open import Cubical.Algebra.AbGroup

-- Reindexing is proved once over an abstract abelian group. The proof is
-- finite Fubini plus a single-entry sum, and uses an actual equivalence.
module FiniteSums (G : AbGroup ℓ-zero) where
  open AbGroupStr (snd G)

  sum : {n : ℕ} → (F.Fin n → fst G) → fst G
  sum {n} = F.sumFinGen {n = n} _+_ 0g

  abstract
    sum-zero : (n : ℕ) → sum {n} (λ _ → 0g) ≡ 0g
    sum-zero n = F.sumFinGen0 _+_ 0g +IdR n (λ _ → 0g) (λ _ → refl)

    sum-add : (n : ℕ) (f g : F.Fin n → fst G)
      → sum {n} (λ i → f i + g i) ≡ sum {n} f + sum {n} g
    sum-add = F.sumFinGenHom _+_ 0g +IdR +Comm +Assoc

    fubini : (m n : ℕ) (f : F.Fin m → F.Fin n → fst G)
      → sum {m} (λ i → sum {n} (f i)) ≡ sum {n} (λ j → sum {m} (λ i → f i j))
    fubini zero n f = sym (sum-zero n)
    fubini (suc m) n f = cong (sum {n} (f (F.flast {k = m})) +_)
      (fubini m n (λ i j → f (F.injectSuc {n = m} i) j))
      ∙ sym (sum-add n (f (F.flast {k = m})) (λ j → sum {m} (λ i → f (F.injectSuc {n = m} i) j)))

  pick : {n : ℕ} → F.Fin n → F.Fin n → fst G → fst G
  pick {n} i j x with F.discreteFin {n} i j
  ... | yes _ = x
  ... | no _ = 0g

  abstract
    pick-hit : {n : ℕ} (i j : F.Fin n) (x : fst G)
      → i ≡ j → pick {n} i j x ≡ x
    pick-hit {n} i j x p with F.discreteFin {n} i j
    ... | yes _ = refl
    ... | no q = Empty.rec (q p)

    pick-miss : {n : ℕ} (i j : F.Fin n) (x : fst G)
      → ¬ (i ≡ j) → pick {n} i j x ≡ 0g
    pick-miss {n} i j x p with F.discreteFin {n} i j
    ... | yes q = Empty.rec (p q)
    ... | no _ = refl

    sum-under-bijection : {m n : ℕ} (e : F.Fin m ≃ F.Fin n)
      (f : F.Fin n → fst G)
      → sum {m} (λ i → f (equivFun e i)) ≡ sum {n} f
    sum-under-bijection {m} {n} e f =
      cong (sum {m}) (funExt λ i → sym (row i))
      ∙ fubini m n matrix
      ∙ cong (sum {n}) (funExt column)
      where
      matrix : F.Fin m → F.Fin n → fst G
      matrix i j = pick {n} (equivFun e i) j (f j)

      row : (i : F.Fin m) → sum {n} (matrix i) ≡ f (equivFun e i)
      row i = F.sumFin-choose _+_ 0g +IdR +Comm {n = n} (matrix i)
        (f (equivFun e i)) (equivFun e i)
        (pick-hit {n} (equivFun e i) (equivFun e i) (f (equivFun e i)) refl)
        (λ j ne → pick-miss {n} (equivFun e i) j (f j) (λ p → ne (sym p)))

      column : (j : F.Fin n) → sum {m} (λ i → matrix i j) ≡ f j
      column j = F.sumFin-choose _+_ 0g +IdR +Comm {n = m} (λ i → matrix i j)
        (f j) (invEq e j) (pick-hit {n} (equivFun e (invEq e j)) j (f j) (secEq e j))
        (λ i ne → pick-miss {n} (equivFun e i) j (f j)
          (λ p → ne (sym (retEq e i) ∙ cong (invEq e) p)))

  -- Proof-free SumFin fold for the certificate's concrete coordinates.
  sumSF : {n : ℕ} → (SF.Fin n → fst G) → fst G
  sumSF {zero} f = 0g
  sumSF {suc n} f = f SF.fzero + sumSF (λ i → f (SF.fsuc i))

  abstract
    sumSF-add : (n : ℕ) (f g : SF.Fin n → fst G)
      → sumSF (λ i → f i + g i) ≡ sumSF f + sumSF g
    sumSF-add zero f g = sym (+IdR 0g)
    sumSF-add (suc n) f g = cong ((f SF.fzero + g SF.fzero) +_)
      (sumSF-add n (λ i → f (SF.fsuc i)) (λ i → g (SF.fsuc i)))
      ∙ AbGroupTheory.comm-4 G (f SF.fzero) (g SF.fzero)
          (sumSF (λ i → f (SF.fsuc i))) (sumSF (λ i → g (SF.fsuc i)))
