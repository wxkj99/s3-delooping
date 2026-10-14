{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient where

-- Collapse the entire vertex pieces, not just cells. The quotient uses
-- CW↪-seam, never a characteristic-map inverse or its right-inverse proof.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; BouquetIso-gen)
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; module prefunctoriality)
open import Cubical.CW.Homotopy using (cofibIso)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)
open import DeloopS3.Bridge.CellularPushout.Vertices using (module Vertices)

module Quotient (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module P = CWPushout ℓ-zero A B C f g
  open Seam A B C f g
  open Vertices A B C f g using (vertexB-cell ; vertexC-cell)

  normalizedMeridian : (n : ℕ) (z : cofibCW n X)
    → Path (Susp (cofibCW n X)) north north
  normalizedMeridian n z = merid z ∙ sym (merid (inl tt))

  prismCollapse : (n : ℕ) → fst Y (suc (suc n)) → Susp (cofibCW n X)
  prismCollapse n (inl b) = north
  prismCollapse n (inr c) = north
  prismCollapse n (push x i) = normalizedMeridian n (inr x) i

  abstract
    prismCollapse-seam : (n : ℕ) (x : fst X n)
      → Path (Path (Susp (cofibCW n X)) north north)
          refl (cong (prismCollapse n ∘ CW↪ Y (suc n)) (push x))
    prismCollapse-seam n x =
      (sym (rCancel (merid (inl tt)))
      ∙ cong (normalizedMeridian n) (push x))
      ∙ sym (cong (cong (prismCollapse n)) (CW↪-seam n x))

    prismCollapse-seam-cancel : (n : ℕ) (x : fst X n)
      → (prismCollapse-seam n x
          ∙ cong (cong (prismCollapse n)) (CW↪-seam n x))
       ≡ (sym (rCancel (merid (inl tt)))
          ∙ cong (normalizedMeridian n) (push x))
    prismCollapse-seam-cancel n x =
      sym (assoc r (sym c) c)
      ∙ cong (r ∙_) (lCancel c)
      ∙ sym (rUnit r)
      where
      r : Path (Path (Susp (cofibCW n X)) north north)
        refl (normalizedMeridian n (inr (CW↪ X n x)))
      r = sym (rCancel (merid (inl tt)))
        ∙ cong (normalizedMeridian n) (push x)
      c : Path (Path (Susp (cofibCW n X)) north north)
        (cong (prismCollapse n ∘ CW↪ Y (suc n)) (push x))
        (normalizedMeridian n (inr (CW↪ X n x)))
      c = cong (cong (prismCollapse n)) (CW↪-seam n x)

    prismCollapse-seam-unfold : (n : ℕ) (x : fst X n)
      → Path
          (Path (Path (Susp (cofibCW n X)) north north)
            refl (cong (prismCollapse n ∘ CW↪ Y (suc n)) (push x)))
          (prismCollapse-seam n x)
          ((sym (rCancel (merid (inl tt)))
            ∙ cong (normalizedMeridian n) (push x))
            ∙ sym (cong (cong (prismCollapse n)) (CW↪-seam n x)))
    prismCollapse-seam-unfold n x = refl

    prismCollapse-seam-cancel-unfold : (n : ℕ) (x : fst X n)
      → let
          r : Path (Path (Susp (cofibCW n X)) north north)
            refl (normalizedMeridian n (inr (CW↪ X n x)))
          r = sym (rCancel (merid (inl tt)))
            ∙ cong (normalizedMeridian n) (push x)
          c : Path (Path (Susp (cofibCW n X)) north north)
            (cong (prismCollapse n ∘ CW↪ Y (suc n)) (push x))
            (normalizedMeridian n (inr (CW↪ X n x)))
          c = cong (cong (prismCollapse n)) (CW↪-seam n x)
        in PathP (λ j → (prismCollapse-seam-unfold n x j ∙ c) ≡ r)
          (prismCollapse-seam-cancel n x)
          (sym (assoc r (sym c) c)
            ∙ cong (r ∙_) (lCancel c)
            ∙ sym (rUnit r))
    prismCollapse-seam-cancel-unfold n x = refl

  prismNull : (n : ℕ) (y : fst Y (suc n))
    → Path (Susp (cofibCW n X)) north (prismCollapse n (CW↪ Y (suc n) y))
  prismNull n (inl b) = refl
  prismNull n (inr c) = refl
  prismNull n (push x i) j = prismCollapse-seam n x j i

  prismRet : (n : ℕ) → cofibCW (suc n) Y → Susp (cofibCW n X)
  prismRet n (inl tt) = north
  prismRet n (inr y) = prismCollapse n y
  prismRet n (push y i) = prismNull n y i

  BQ : (T : CWskel ℓ-zero) (n : ℕ)
    → Iso (cofibCW n T) (SphereBouquet n (Fin (snd T .fst n)))
  BQ T n = BouquetIso-gen n (snd T .fst n)
    (snd T .snd .fst n) (snd T .snd .snd .snd n)

  R : (n : ℕ) → AbGroupHom (Z Y (suc n)) (Z X n)
  R n = bouquetDegree
    (Iso.fun (cofibIso n X) ∘ prismRet n ∘ Iso.inv (BQ Y (suc n)))

  private
    qB : (n : ℕ) → cofibCW (suc n) YB → cofibCW (suc n) Y
    qB n = prefunctoriality.fn+1/fn (suc (suc n))
      (restrictCell vertexB-cell (suc (suc n))) (suc n , <ᵗsuc)

    qC : (n : ℕ) → cofibCW (suc n) YC → cofibCW (suc n) Y
    qC n = prefunctoriality.fn+1/fn (suc (suc n))
      (restrictCell vertexC-cell (suc (suc n))) (suc n , <ᵗsuc)

  abstract
    prismRet-VB : (n : ℕ)
      → prismRet n ∘ qB n ≡ (λ _ → north)
    prismRet-VB n = funExt λ
      { (inl tt) → refl
      ; (inr b) → refl
      ; (push b i) j →
          (cong-∙ (prismRet n) (push (inl b)) refl
            ∙ sym (rUnit refl)) j i }

    prismRet-VC : (n : ℕ)
      → prismRet n ∘ qC n ≡ (λ _ → north)
    prismRet-VC n = funExt λ
      { (inl tt) → refl
      ; (inr c) → refl
      ; (push c i) j →
          (cong-∙ (prismRet n) (push (inr c)) refl
            ∙ sym (rUnit refl)) j i }

    cofibIso-north : (n : ℕ)
      → Iso.fun (cofibIso n X) north ≡ inl tt
    cofibIso-north zero = refl
    cofibIso-north (suc n) = refl

    R-VB : (n : ℕ)
      → compGroupHom (VB (suc n)) (R n) ≡ trivGroupHom
    R-VB n =
      sym (bouquetDegreeComp
        (Iso.fun (cofibIso n X) ∘ prismRet n ∘ Iso.inv (BQ Y (suc n)))
        (Iso.fun (BQ Y (suc n)) ∘ qB n ∘ Iso.inv (BQ YB (suc n))))
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso n X) ∘ prismRet n)
            (Iso.ret (BQ Y (suc n)) (qB n (Iso.inv (BQ YB (suc n)) z)))
          ∙ cong (Iso.fun (cofibIso n X))
              (funExt⁻ (prismRet-VB n) (Iso.inv (BQ YB (suc n)) z))
          ∙ cofibIso-north n)
      ∙ bouquetDegreeConst (suc n) (snd YB .fst (suc n)) (snd X .fst n)

    R-VC : (n : ℕ)
      → compGroupHom (VC (suc n)) (R n) ≡ trivGroupHom
    R-VC n =
      sym (bouquetDegreeComp
        (Iso.fun (cofibIso n X) ∘ prismRet n ∘ Iso.inv (BQ Y (suc n)))
        (Iso.fun (BQ Y (suc n)) ∘ qC n ∘ Iso.inv (BQ YC (suc n))))
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso n X) ∘ prismRet n)
            (Iso.ret (BQ Y (suc n)) (qC n (Iso.inv (BQ YC (suc n)) z)))
          ∙ cong (Iso.fun (cofibIso n X))
              (funExt⁻ (prismRet-VC n) (Iso.inv (BQ YC (suc n)) z))
          ∙ cofibIso-north n)
      ∙ bouquetDegreeConst (suc n) (snd YC .fst (suc n)) (snd X .fst n)
