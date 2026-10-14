{-# OPTIONS --cubical --safe #-}

module DeloopS3.Bridge.DegreeSpan.TopCubeAssembleAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (Square→compPath; compPath→Square)
open import Cubical.Foundations.GroupoidLaws using (assoc; lUnit; rUnit; rCancel)

private
  variable
    ℓ : Level

abstract
  pasting-square :
    {B : Type ℓ} {a low high m0 m1 src : B}
    (v : a ≡ low) (c : low ≡ high)
    (g0 : low ≡ m0) (g1 : high ≡ m1) (u : m0 ≡ m1)
    (n : a ≡ m0) (b : a ≡ src) (e : src ≡ m1)
    (lower : v ∙ g0 ≡ n)
    (middle : g0 ∙ u ≡ c ∙ g1)
    (overlap-square : Square b (n ∙ u) refl e)
    → Square (v ∙ c) b refl (g1 ∙ sym e)
  pasting-square v c g0 g1 u n b e lower middle overlap-square =
    compPath→Square (sym (lUnit b) ∙ sym R)
    where
    H : (v ∙ c) ∙ g1 ≡ b ∙ e
    H = sym (assoc v c g1)
      ∙ cong (v ∙_) (sym middle)
      ∙ assoc v g0 u
      ∙ cong (_∙ u) lower
      ∙ lUnit (n ∙ u)
      ∙ Square→compPath overlap-square

    R : (v ∙ c) ∙ (g1 ∙ sym e) ≡ b
    R = assoc (v ∙ c) g1 (sym e)
      ∙ cong (_∙ sym e) H
      ∙ sym (assoc b e (sym e))
      ∙ cong (b ∙_) (rCancel e)
      ∙ sym (rUnit b)

  exact-unit-cube :
    (Z : Type ℓ) (z : Z)
    → let L = Path Z z z in
      {low high src : L}
      (v : Path L refl low) (c : Path L low high)
      (b : Path L refl src) (h : Path L high src)
      (Q : Square {A = L} (v ∙ c) b refl h)
      → PathP
          (λ k → Square {A = Z}
            ((λ j → v j k) ∙ (λ j → c j k))
            (λ j → b j k) refl (λ t → h t k))
          (sym (rUnit (refl {x = z})))
          (sym (rUnit (refl {x = z})))
  exact-unit-cube Z z v c b h Q k t j =
    hcomp
      (λ r → λ
        { (t = i0) → E k (~ r) j
        ; (t = i1) → b j k
        ; (j = i0) → z
        ; (j = i1) → h t k
        ; (k = i0) → compPath-filler (refl {x = z}) refl (r ∧ ~ t) j
        ; (k = i1) → compPath-filler (refl {x = z}) refl (r ∧ ~ t) j
        })
      (Q t j k)
    where
    E : (k : I) → Square {A = Z}
      ((λ j → v j k) ∙ (λ j → c j k))
      (λ j → (v ∙ c) j k) refl refl
    E k t j =
      hcomp
        (λ r → λ
          { (t = i0) → compPath-filler (λ j → v j k) (λ j → c j k) r j
          ; (t = i1) → compPath-filler v c r j k
          ; (j = i0) → z
          ; (j = i1) → c r k
          ; (k = i0) → compPath-filler (refl {x = z}) refl (r ∧ ~ t) j
          ; (k = i1) → compPath-filler (refl {x = z}) refl (r ∧ ~ t) j
          })
        (v j k)
