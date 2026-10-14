{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFreeMatrix where

-- Paper proof: diagonalize one pivot, not the whole matrix.  For a block
-- a ⊕ D, a left inverse supplies b*a = 1 and E*D = I.  Commutativity
-- makes b a two-sided scalar inverse; induction makes D invertible.
-- Hence b ⊕ D⁻¹ is a two-sided inverse.  Invertible changes of basis
-- preserve this argument.  Finally a specified left inverse equals the
-- constructed inverse.  No determinant or determinant multiplicativity.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
open import Cubical.Data.Int using (ℤ ; injPos)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.IntegerMatrix.Diagonalization using (DiagStep ; diagStep)

open CommRingStr (ℤCommRing .snd)
open RingTheory (CommRing→Ring ℤCommRing)
open Coefficient ℤCommRing
open Sum (CommRing→Ring ℤCommRing)
open Sim
open SimRel

private
  variable n : ℕ

  inverse-invertible : {M : Mat n n} (p : isInv M) → isInv (p .fst)
  inverse-invertible {M = M} p = M , p .snd .snd , p .snd .fst

  cancel-sandwich : (L M R Li Ri : Mat n n)
    → Li ⋆ L ≡ 𝟙 → R ⋆ Ri ≡ 𝟙
    → Li ⋆ (L ⋆ M ⋆ R) ⋆ Ri ≡ M
  cancel-sandwich L M R Li Ri l r =
      cong (_⋆ Ri) (⋆Assoc Li (L ⋆ M) R)
    ∙ cong (λ X → X ⋆ R ⋆ Ri) (⋆Assoc Li L M)
    ∙ cong (λ X → (X ⋆ M) ⋆ R ⋆ Ri) l
    ∙ cong (λ X → X ⋆ R ⋆ Ri) (⋆lUnit M)
    ∙ sym (⋆Assoc M R Ri)
    ∙ cong (M ⋆_) r
    ∙ ⋆rUnit M

  change-left : (M B : Mat n n) → B ⋆ M ≡ 𝟙
    → (s : Sim M) → Σ[ C ∈ Mat n n ] C ⋆ s .result ≡ 𝟙
  change-left M B p s = C , proof
    where
    L = s .simrel .transMatL
    R = s .simrel .transMatR
    Li = s .simrel .isInvTransL .fst
    Ri = s .simrel .isInvTransR .fst
    C = Ri ⋆ B ⋆ Li
    proof : C ⋆ s .result ≡ 𝟙
    proof = cong (C ⋆_) (s .simrel .transEq)
      ∙ sym (⋆Assoc (Ri ⋆ B) Li (L ⋆ M ⋆ R))
      ∙ cong ((Ri ⋆ B) ⋆_) (⋆Assoc Li (L ⋆ M) R)
      ∙ cong (λ X → (Ri ⋆ B) ⋆ (X ⋆ R)) (⋆Assoc Li L M)
      ∙ cong (λ X → (Ri ⋆ B) ⋆ ((X ⋆ M) ⋆ R))
          (s .simrel .isInvTransL .snd .snd)
      ∙ cong (λ X → (Ri ⋆ B) ⋆ (X ⋆ R)) (⋆lUnit M)
      ∙ sym (⋆Assoc Ri B (M ⋆ R))
      ∙ cong (Ri ⋆_) (⋆Assoc B M R)
      ∙ cong (λ X → Ri ⋆ (X ⋆ R)) p
      ∙ cong (Ri ⋆_) (⋆lUnit R)
      ∙ s .simrel .isInvTransR .snd .snd

  change-invertible : {M : Mat n n} (s : Sim M)
    → isInv (s .result) → isInv M
  change-invertible {M = M} s q = subst isInv undo inv
    where
    L = s .simrel .transMatL
    R = s .simrel .transMatR
    Li = s .simrel .isInvTransL .fst
    Ri = s .simrel .isInvTransR .fst
    undo : Li ⋆ s .result ⋆ Ri ≡ M
    undo = cong (λ X → Li ⋆ X ⋆ Ri) (s .simrel .transEq)
      ∙ cancel-sandwich L M R Li Ri
          (s .simrel .isInvTransL .snd .snd)
          (s .simrel .isInvTransR .snd .fst)
    inv : isInv (Li ⋆ s .result ⋆ Ri)
    inv = isInv⋆ (isInv⋆ (inverse-invertible (s .simrel .isInvTransL)) q)
      (inverse-invertible (s .simrel .isInvTransR))

  clean-block : {M : Mat (suc n) (suc n)} (d : DiagStep M)
    → d .DiagStep.sim .result
      ≡ d .DiagStep.sim .result zero zero ⊕ sucMat (d .DiagStep.sim .result)
  clean-block d i zero zero = d .DiagStep.sim .result zero zero
  clean-block d i zero (suc j) = d .DiagStep.firstRowClean j i
  clean-block d i (suc j) zero = d .DiagStep.firstColClean j i
  clean-block d i (suc j) (suc k) = d .DiagStep.sim .result (suc j) (suc k)

  block-scalar : (a : ℤ) (D : Mat n n) (B : Mat (suc n) (suc n))
    → B ⋆ (a ⊕ D) ≡ 𝟙 → B zero zero · a ≡ 1r
  block-scalar a D B p =
      sym (cong (B zero zero · a +_) (∑Mulr0 (λ j → B zero (suc j)))
        ∙ +IdR (B zero zero · a))
    ∙ cong (λ X → X zero zero) p

  block-tail : (a : ℤ) (D : Mat n n) (B : Mat (suc n) (suc n))
    → B ⋆ (a ⊕ D) ≡ 𝟙 → sucMat B ⋆ D ≡ 𝟙
  block-tail a D B p = funExt λ i → funExt λ j →
      sym (cong (_+ (sucMat B ⋆ D) i j) (0RightAnnihilates (B (suc i) zero))
        ∙ +IdL ((sucMat B ⋆ D) i j))
    ∙ cong (λ X → X (suc i) (suc j)) p
    ∙ sym (𝟙suc i j)

  block-invertible : (a b : ℤ) (D : Mat n n)
    → b · a ≡ 1r → isInv D → isInv (a ⊕ D)
  block-invertible a b D p q = (b ⊕ q .fst) ,
      (⊕-⋆ a b D (q .fst)
        ∙ (λ i → (·Comm a b ∙ p) i ⊕ q .snd .fst i) ∙ 1⊕𝟙) ,
      (⊕-⋆ b a (q .fst) D
        ∙ (λ i → p i ⊕ q .snd .snd i) ∙ 1⊕𝟙)

  left-invertible : (n : ℕ) (M B : Mat n n) → B ⋆ M ≡ 𝟙 → isInv M
  left-invertible zero M B p = 𝟙 , (funExt λ ()) , (funExt λ ())
  left-invertible (suc n) M B p with diagStep M
  ... | inr z = Empty.rec (znots (injPos zero≡one))
    where
    zero≡one : 0r ≡ 1r
    zero≡one = sym (∑Mulr0 (B zero))
      ∙ cong (λ X → (B ⋆ X) zero zero) (sym z)
      ∙ cong (λ X → X zero zero) p
  ... | inl d = change-invertible (d .DiagStep.sim)
      (subst isInv (sym (clean-block d))
        (block-invertible a (C zero zero) D (block-scalar a D C q)
          (left-invertible n D (sucMat C) (block-tail a D C q))))
    where
    a = d .DiagStep.sim .result zero zero
    D = sucMat (d .DiagStep.sim .result)
    changed = change-left M B p (d .DiagStep.sim)
    C = changed .fst
    q : C ⋆ (a ⊕ D) ≡ 𝟙
    q = cong (C ⋆_) (sym (clean-block d)) ∙ changed .snd

integer-matrix-direct-finite : (n : ℕ) (M B : Mat n n)
  → B ⋆ M ≡ 𝟙 → M ⋆ B ≡ 𝟙
integer-matrix-direct-finite n M B p = cong (M ⋆_) unique ∙ q .snd .fst
  where
  q = left-invertible n M B p
  unique : B ≡ q .fst
  unique = sym (⋆rUnit B)
    ∙ cong (B ⋆_) (sym (q .snd .fst))
    ∙ ⋆Assoc B M (q .fst)
    ∙ cong (_⋆ q .fst) p
    ∙ ⋆lUnit (q .fst)
