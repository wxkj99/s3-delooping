{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeNull where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; rCancel)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; merid)
open import Cubical.CW.Base using (CWskel ; CW↪ ; cofibCW)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient
  using (module Quotient)
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)

module TopCubeNull (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  module Q = Quotient A B C f g
  module S = Seam A B C f g

  abstract
    seam-correction-null : (n : ℕ) (x : fst S.X n)
      → Path
          (Path (Path (Susp (cofibCW n S.X)) north north)
            (cong (Q.prismCollapse n ∘ CW↪ S.Y (suc n)) (push x))
            (Q.normalizedMeridian n (inr (CW↪ S.X n x))))
          (cong (cong (Q.prismCollapse n)) (S.CW↪-seam n x))
          refl
    seam-correction-null n x =
      cong (cong (cong (Q.prismCollapse n))) (S.CW↪-seam-null n x)

    prismNull-seam-normal : (n : ℕ) (x : fst S.X n)
      → Path
          (Path (Path (Susp (cofibCW n S.X)) north north)
            refl
            (cong (Q.prismCollapse n ∘ CW↪ S.Y (suc n)) (push x)))
          (Q.prismCollapse-seam n x)
          (sym (rCancel (merid (inl tt)))
            ∙ cong (Q.normalizedMeridian n) (push x))
    prismNull-seam-normal n x =
      rUnit (Q.prismCollapse-seam n x)
      ∙ cong (Q.prismCollapse-seam n x ∙_) (sym (seam-correction-null n x))
      ∙ Q.prismCollapse-seam-cancel n x

    null-on-seam : (n : ℕ) (x : fst S.X n)
      → Path
          (Path (Path (Susp (cofibCW n S.X)) north north)
            refl
            (cong (Q.prismCollapse n ∘ CW↪ S.Y (suc n)) (push x)))
          (λ j i → Q.prismNull n (push x i) j)
          (sym (rCancel (merid (inl tt)))
            ∙ cong (Q.normalizedMeridian n) (push x))
    null-on-seam n x = prismNull-seam-normal n x
