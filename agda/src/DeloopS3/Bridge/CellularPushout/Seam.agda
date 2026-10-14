{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.Seam where

-- The specified pushout seam, its cellular coherence, and the library's
-- chain-homotopy boundary formula.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lCancel)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.Algebra.AbGroup
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; composeCellMap)
open import Cubical.CW.Homotopy using (cellHom ; module preChainHomotopy)
open import Cubical.CW.ChainComplex using (∂)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.Vertices using (module Vertices)

module Seam (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module P = CWPushout ℓ-zero A B C f g
  open Vertices A B C f g using (vertexB-cell ; vertexC-cell)

  X YB YC Y : CWskel ℓ-zero
  X = P.B
  YB = P.C
  YC = P.D
  Y = P.pushoutSkel

  F G : cellMap X Y
  F = composeCellMap vertexB-cell P.f
  G = composeCellMap vertexC-cell P.g

  abstract
    -- SeqIs compares the sequence pushout's composite path with CW↪.
    -- Its endpoint corrections are strict, but its unit fillers are not
    -- discarded: first reverse that comparison, then use the specified
    -- double-composition filler to reach the literal next-stage seam.
    CW↪-seam : (n : ℕ) (x : fst X n)
      → Square {A = fst Y (suc (suc n))}
          (cong (CW↪ Y (suc n)) (push x))
          (push (CW↪ X n x)) refl refl
    CW↪-seam n x =
      sym (λ j i → snd P.SeqIs n (push x i) j)
      ∙ (λ j i → doubleCompPath-filler refl
          (push (CW↪ X n x)) refl (~ j) i)

    -- P.f and P.g are strictified, so the `comm` fields inside SeqIs are
    -- `refl`. Both summands of CW↪-seam are the same square u, and
    -- CW↪-seam = sym u ∙ u is null by lCancel.
    CW↪-seam-null : (n : ℕ) (x : fst X n)
      → CW↪-seam n x ≡ refl
    CW↪-seam-null n x = lCancel
      (λ j i → doubleCompPath-filler refl (push (CW↪ X n x)) refl (~ j) i)

    CW↪-seam-unfold : (n : ℕ) (x : fst X n)
      → Path
          (Square {A = fst Y (suc (suc n))}
            (cong (CW↪ Y (suc n)) (push x))
            (push (CW↪ X n x)) refl refl)
          (CW↪-seam n x)
          (sym (λ j i → doubleCompPath-filler refl
              (push (CW↪ X n x)) refl (~ j) i)
            ∙ (λ j i → doubleCompPath-filler refl
                (push (CW↪ X n x)) refl (~ j) i))
    CW↪-seam-unfold n x = refl

    CW↪-seam-null-unfold : (n : ℕ) (x : fst X n)
      → PathP (λ j → CW↪-seam-unfold n x j ≡ refl)
          (CW↪-seam-null n x)
          (lCancel (λ j i → doubleCompPath-filler refl
            (push (CW↪ X n x)) refl (~ j) i))
    CW↪-seam-null-unfold n x = refl

  private
    -- Composition of cellular maps has comm = refl ∙ refl at these
    -- stages. Keep the two rUnit fillers when changing the square's
    -- vertical sides; they are not definitionally constant paths.
    -- This adapter stays transparent so seam.coh reduces to the exported
    -- CW↪-seam square, whose expensive SeqIs proof is abstract above.
    seam-coherence₊ : (n : ℕ) (x : fst X (suc n))
      → Square {A = fst Y (suc (suc (suc n)))}
          (cong (CW↪ Y (suc (suc n))) (push x))
          (push (CW↪ X (suc n) x))
          (cong (CW↪ Y (suc (suc n))) (SequenceMap.comm F (suc n) x))
          (cong (CW↪ Y (suc (suc n))) (SequenceMap.comm G (suc n) x))
    seam-coherence₊ n x = subst2
      (λ l r → Square {A = fst Y (suc (suc (suc n)))}
        (cong (CW↪ Y (suc (suc n))) (push x))
        (push (CW↪ X (suc n) x)) l r)
      (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
      (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
      (CW↪-seam (suc n) x)

  seam : cellHom F G
  cellHom.hom seam zero x = Empty.rec (snd X .snd .snd .fst x)
  cellHom.hom seam (suc n) x = push x
  cellHom.coh seam zero x = Empty.rec (snd X .snd .snd .fst x)
  cellHom.coh seam (suc n) x = seam-coherence₊ n x

  private
    module H (n : ℕ) = preChainHomotopy (suc n) X Y
      (restrictCell F (suc n)) (restrictCell G (suc n))
      (restrictCellHom seam (suc n)) (n , <ᵗsuc)

  HC : (n : ℕ) → Susp (cofibCW n X) → cofibCW (suc n) Y
  HC n = H.Hn+1/Hn n

  KBouquet : (n : ℕ)
    → SphereBouquet (suc n) (Fin (snd X .fst n))
    → SphereBouquet (suc n) (Fin (snd Y .fst (suc n)))
  KBouquet n = H.bouquetHomotopy n

  K : (n : ℕ) → AbGroupHom (Z X n) (Z Y (suc n))
  K n = H.chainHomotopy n

  VB : (n : ℕ) → AbGroupHom (Z YB n) (Z Y n)
  VB = cellular-coefficients vertexB-cell

  VC : (n : ℕ) → AbGroupHom (Z YC n) (Z Y n)
  VC = cellular-coefficients vertexC-cell

  abstract
    K-boundary₀ :
      compGroupHom (K 0) (∂ Y 0)
      ≡ subtrGroupHom (Z X 0) (Z Y 0)
          (compGroupHom (cellular-coefficients P.f 0) (VB 0))
          (compGroupHom (cellular-coefficients P.g 0) (VC 0))
    K-boundary₀ = homotopy-boundary₀ seam
      ∙ cong₂ (subtrGroupHom (Z X 0) (Z Y 0))
          (cellular-coefficients-comp vertexB-cell P.f 0)
          (cellular-coefficients-comp vertexC-cell P.g 0)

    K-boundary₊ : (n : ℕ)
      → compGroupHom (K (suc n)) (∂ Y (suc n))
       ≡ subtrGroupHom (Z X (suc n)) (Z Y (suc n))
           (subtrGroupHom (Z X (suc n)) (Z Y (suc n))
             (compGroupHom (cellular-coefficients P.f (suc n)) (VB (suc n)))
             (compGroupHom (cellular-coefficients P.g (suc n)) (VC (suc n))))
           (compGroupHom (∂ X n) (K n))
    K-boundary₊ n = homotopy-boundary₊ seam n
      ∙ cong (λ h → subtrGroupHom (Z X (suc n)) (Z Y (suc n))
          h (compGroupHom (∂ X n) (K n)))
          (cong₂ (subtrGroupHom (Z X (suc n)) (Z Y (suc n)))
            (cellular-coefficients-comp vertexB-cell P.f (suc n))
            (cellular-coefficients-comp vertexC-cell P.g (suc n)))
