{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismRetraction.Homotopy where

-- The merid(push x j) cube is factored into naturality of the specified
-- hfill, pasting in loop space, and cancellation of CW↪-seam.  No claim
-- that a filler with constant boundary is unique is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient using (module Quotient)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.StrictHC using (module StrictHC)

module Homotopy (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module P = CWPushout ℓ-zero A B C f g
  open Seam A B C f g
  open Quotient A B C f g
  open StrictHC A B C f g
  open SequenceMap

  private
    T : ℕ → Type
    T n = Susp (cofibCW n X)

    seamImage : (n : ℕ) (x : fst X n)
      → Path (Path (T n) north north)
          (cong (prismCollapse n ∘ CW↪ Y (suc n)) (push x))
          (normalizedMeridian n (inr (CW↪ X n x)))
    seamImage n x = cong (cong (prismCollapse n)) (CW↪-seam n x)

    oldFill : (n : ℕ) (x : fst X n) → I → I → I → cofibCW (suc n) Y
    oldFill n x j i k = hfill (λ k → λ
      { (i = i0) → push (inl (map P.f (suc n) (CW↪ X n x))) (~ k)
      ; (i = i1) → push (inr (map P.g (suc n) (CW↪ X n x))) (~ k)
      ; (j = i0) → push (push x i) (~ k) })
      (inS (inr (CW↪-seam n x j i))) k

    imageFill : (n : ℕ) (x : fst X n) → I → I → I → T n
    imageFill n x j i k = hfill (λ k → λ
      { (i = i0) → north
      ; (i = i1) → north
      ; (j = i0) → prismCollapse-seam n x (~ k) i })
      (inS (seamImage n x j i)) k

    imageHC : (n : ℕ) → T n → T n
    imageHC n north = north
    imageHC n south = north
    imageHC n (merid (inl tt) i) = north
    imageHC n (merid (inr x) i) =
      (refl ∙∙ normalizedMeridian n (inr x) ∙∙ refl) i
    imageHC n (merid (push x j) i) = imageFill n x j i i1

    loopExtension : (n : ℕ)
      → ((x : fst X n) → Path (Path (T n) north north)
           refl (normalizedMeridian n (inr (CW↪ X n x))))
      → T n → T n
    loopExtension n s north = north
    loopExtension n s south = north
    loopExtension n s (merid (inl tt) i) = north
    loopExtension n s (merid (inr x) i) = normalizedMeridian n (inr x) i
    loopExtension n s (merid (push x j) i) = s x j i

    pasted : (n : ℕ) (x : fst X n)
      → Path (Path (T n) north north)
          refl (normalizedMeridian n (inr (CW↪ X n x)))
    pasted n x = prismCollapse-seam n x ∙' seamImage n x

    canonical : (n : ℕ) (x : fst X n)
      → Path (Path (T n) north north)
          refl (normalizedMeridian n (inr (CW↪ X n x)))
    canonical n x = sym (rCancel (merid (inl tt)))
      ∙ cong (normalizedMeridian n) (push x)

    normalSusp : (n : ℕ) → T n → T n
    normalSusp n north = north
    normalSusp n south = north
    normalSusp n (merid z i) = normalizedMeridian n z i

  abstract
    private
      postcomposeHC : (n : ℕ) → prismRet n ∘ HC-strict n ≡ imageHC n
      postcomposeHC n = funExt λ
        { north → refl
        ; south → refl
        ; (merid (inl tt) i) → refl
        ; (merid (inr x) i) t →
            cong-∙∙ (prismRet n)
              (push (inl (map P.f (suc n) x)))
              (cong (to_cofibCW (suc n) Y) (push x))
              (sym (push (inr (map P.g (suc n) x)))) t i
        ; (merid (push x j) i) t →
            hcomp (λ k → λ
              { (t = i0) → prismRet n (oldFill n x j i k)
              ; (t = i1) → imageFill n x j i k
              ; (i = i0) → north
              ; (i = i1) → north
              ; (j = i0) → prismCollapse-seam n x (~ k) i })
              (seamImage n x j i) }

      imageHC-paste : (n : ℕ) → imageHC n ≡ loopExtension n (pasted n)
      imageHC-paste n = funExt λ
        { north → refl
        ; south → refl
        ; (merid (inl tt) i) → refl
        ; (merid (inr x) i) t →
            doubleCompPath-filler refl (normalizedMeridian n (inr x)) refl (~ t) i
        ; (merid (push x j) i) t →
            hcomp (λ k → λ
              { (t = i0) → imageFill n x j i k
              ; (t = i1) → compPath'-filler
                  (prismCollapse-seam n x) (seamImage n x) k j i
              ; (i = i0) → north
              ; (i = i1) → north
              ; (j = i0) → prismCollapse-seam n x (~ k) i
              ; (j = i1) → doubleCompPath-filler refl
                  (normalizedMeridian n (inr (CW↪ X n x))) refl (k ∧ ~ t) i })
              (seamImage n x j i) }

      paste-canonical : (n : ℕ)
        → loopExtension n (pasted n) ≡ loopExtension n (canonical n)
      paste-canonical n = cong (loopExtension n) (funExt λ x →
        sym (compPath≡compPath' (prismCollapse-seam n x) (seamImage n x))
        ∙ prismCollapse-seam-cancel n x)

      canonical-normal : (n : ℕ)
        → loopExtension n (canonical n) ≡ normalSusp n
      canonical-normal n = funExt λ
        { north → refl
        ; south → refl
        ; (merid (inl tt) i) t → rCancel (merid (inl tt)) (~ t) i
        ; (merid (inr x) i) → refl
        ; (merid (push x j) i) t →
            compPath-filler' (sym (rCancel (merid (inl tt))))
              (cong (normalizedMeridian n) (push x)) (~ t) j i }

      normal-id : (n : ℕ) → normalSusp n ≡ idfun (T n)
      normal-id n = funExt λ
        { north → refl
        ; south → merid (inl tt)
        ; (merid z i) t → compPath-filler (merid z)
            (sym (merid (inl tt))) (~ t) i }

    prismRet-H : (n : ℕ) → prismRet n ∘ HC n ≡ idfun (Susp (cofibCW n X))
    prismRet-H n = cong (prismRet n ∘_) (sym (HC-strict≡HC n))
      ∙ postcomposeHC n
      ∙ imageHC-paste n
      ∙ paste-canonical n
      ∙ canonical-normal n
      ∙ normal-id n
