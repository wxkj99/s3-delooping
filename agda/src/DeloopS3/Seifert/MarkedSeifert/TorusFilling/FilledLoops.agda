{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Filled-loop equations in the actual pushout.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos; ·IdR)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
open import DeloopS3.Move.CancelMinimal using (C; 0C; mulC; _+C_)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill)

abstract
  square-based : {ℓ : Level} {X : Type ℓ} {a b : X}
    (p : a ≡ b) (l : a ≡ a) (k : b ≡ b)
    → Square p p l k → based p l ≡ k
  square-based p l k s = sym (assoc (sym p) l p)
    ∙ cong (sym p ∙_) (Square→compPath s)
    ∙ assoc (sym p) p k ∙ cong (_∙ k) (lCancel p) ∙ sym (lUnit k)

  based-sym : {ℓ : Level} {X : Type ℓ} {a b : X}
    (p : a ≡ b) (l : a ≡ a) → based p (sym l) ≡ sym (based p l)
  based-sym p l = sym (assoc (sym p) (sym l) p)
    ∙ sym (symDistr (sym p ∙ l) p
      ∙ cong (sym p ∙_) (symDistr (sym p) l))

module Filling (e : ℤ) where
  include : Kinv → Fill e
  include = inl

  core : C → Fill e
  core = inr

  coreBase : Fill e
  coreBase = core 0C

  seam : inl kbase ≡ coreBase
  seam = push (0C , 0C)

  jFilled rFilled hFilled xFilled yFilled z : coreBase ≡ coreBase
  jFilled = based seam (cong include j)
  rFilled = based seam (cong include r)
  hFilled = based seam (cong include (j ∙ j))
  xFilled = jFilled
  yFilled = based seam (cong include (j ∙ sym r))
  z = cong core hC

  -- Integer powers are the literal images of emloop n, not π₁ classes.
  zPower : ℤ → coreBase ≡ coreBase
  zPower n = cong core (emloop n)

  abstract
    row-u : cong (row e (pos 1)) uT ≡ emloop e
    row-u = cong emloop (·IdR e)

    row-v : cong (row e (pos 1)) vT ≡ hC
    row-v = refl

    attach-u : based seam (cong include (cong λ₂ uT))
      ≡ cong core (cong (row e (pos 1)) uT)
    attach-u = square-based seam
      (cong include (cong λ₂ uT)) (cong core (cong (row e (pos 1)) uT))
      (λ i k → push (uT i) k)

    attach-v : based seam (cong include (cong λ₂ vT))
      ≡ cong core (cong (row e (pos 1)) vT)
    attach-v = square-based seam
      (cong include (cong λ₂ vT)) (cong core (cong (row e (pos 1)) vT))
      (λ i k → push (vT i) k)

    h-is-zPower-e : hFilled ≡ zPower e
    h-is-zPower-e = cong (based seam) (cong (cong include) (sym λ₂-u))
      ∙ attach-u ∙ cong (cong core) row-u

    fibre-is-core : rFilled ≡ z
    fibre-is-core = cong (based seam) (cong (cong include) (sym λ₂-v))
      ∙ attach-v ∙ cong (cong core) row-v

    h-is-j-squared : hFilled ≡ jFilled ∙ jFilled
    h-is-j-squared = cong (based seam) (cong-∙ include j j)
      ∙ based-comp seam (cong include j) (cong include j)

    x-is-j : xFilled ≡ jFilled
    x-is-j = refl

    -- y is the retained old Seifert core word, not the new fibre.
    y-is-j-r-inverse : yFilled ≡ jFilled ∙ sym rFilled
    y-is-j-r-inverse = cong (based seam) (cong-∙ include j (sym r))
      ∙ based-comp seam (cong include j) (cong include (sym r))
      ∙ cong (jFilled ∙_) (based-sym seam (cong include r))

    j-squared-is-zPower-e : jFilled ∙ jFilled ≡ zPower e
    j-squared-is-zPower-e = sym h-is-j-squared ∙ h-is-zPower-e
