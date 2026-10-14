{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismRetraction.StrictHC where

-- Keep the unit-path corrections in Seam.seam.coh.  The transport filler
-- compares the actual HC with a presentation having constant vertical
-- edges; it does not replace a specified square by an arbitrary filler.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)

module StrictHC (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module P = CWPushout ℓ-zero A B C f g
  open Seam A B C f g
  open SequenceMap

  HC-meridian : (n : ℕ) (x : fst X (suc n))
    → Path (cofibCW (suc n) Y) (inl tt) (inl tt)
  HC-meridian n x = left ∙∙ middle ∙∙ sym right
    where
    left : Path (cofibCW (suc n) Y) (inl tt)
      (inr (CW↪ Y (suc n) (inl (map P.f (suc n) x))))
    left = push (inl (map P.f (suc n) x))
    right : Path (cofibCW (suc n) Y) (inl tt)
      (inr (CW↪ Y (suc n) (inr (map P.g (suc n) x))))
    right = push (inr (map P.g (suc n) x))
    middle : Path (cofibCW (suc n) Y)
      (inr (CW↪ Y (suc n) (inl (map P.f (suc n) x))))
      (inr (CW↪ Y (suc n) (inr (map P.g (suc n) x))))
    middle = cong (to_cofibCW (suc n) Y) (push x)

  HC-strict : (n : ℕ) → Susp (cofibCW n X) → cofibCW (suc n) Y
  HC-strict n north = inl tt
  HC-strict n south = inl tt
  HC-strict n (merid (inl tt) i) = inl tt
  HC-strict n (merid (inr x) i) = HC-meridian n x i
  HC-strict n (merid (push x j) i) =
    hcomp (λ k → λ
      { (i = i0) → push (inl (map P.f (suc n) (CW↪ X n x))) (~ k)
      ; (i = i1) → push (inr (map P.g (suc n) (CW↪ X n x))) (~ k)
      ; (j = i0) → push (push x i) (~ k) })
      (inr (CW↪-seam n x j i))

  abstract
    HC-strict≡HC : (n : ℕ) → HC-strict n ≡ HC n
    HC-strict≡HC n = funExt (go n)
      where
      cohFill : (n : ℕ) (x : fst X (suc n))
        → PathP (λ t → Square
            (cong (CW↪ Y (suc (suc n))) (push x))
            (push (CW↪ X (suc n) x))
            (cong (CW↪ Y (suc (suc n)))
              (rUnit (refl {x = inl (inl (map P.f (suc n) x))}) t))
            (cong (CW↪ Y (suc (suc n)))
              (rUnit (refl {x = inr (inl (map P.g (suc n) x))}) t)))
          (CW↪-seam (suc n) x)
          (subst2
            (λ l r → Square
              (cong (CW↪ Y (suc (suc n))) (push x))
              (push (CW↪ X (suc n) x)) l r)
            (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
            (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
            (CW↪-seam (suc n) x))
      cohFill n x = subst2-filler
        (λ l r → Square
          (cong (CW↪ Y (suc (suc n))) (push x))
          (push (CW↪ X (suc n) x)) l r)
        (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
        (cong (cong (CW↪ Y (suc (suc n)))) (rUnit refl))
        (CW↪-seam (suc n) x)

      squareCompare : (n : ℕ) (x : fst X n)
        → Path (Square {A = cofibCW (suc n) Y}
            refl (HC-meridian n (CW↪ X n x)) refl refl)
          (λ j i → HC-strict n (merid (push x j) i))
          (λ j i → HC n (merid (push x j) i))
      squareCompare zero x = Empty.rec (snd X .snd .snd .fst x)
      squareCompare (suc n) x t j i =
        hcomp (λ k → λ
          { (i = i0) → push (rUnit (refl {x = inl (inl (map P.f (suc n) x))}) t j) (~ k)
          ; (i = i1) → push (rUnit (refl {x = inr (inl (map P.g (suc n) x))}) t j) (~ k)
          ; (j = i0) → push (push x i) (~ k) })
          (inr (cohFill n x t j i))

      go : (n : ℕ) (z : Susp (cofibCW n X)) → HC-strict n z ≡ HC n z
      go n north = refl
      go n south = refl
      go n (merid (inl tt) i) = refl
      go n (merid (inr x) i) = refl
      go n (merid (push x j) i) t = squareCompare n x t j i
