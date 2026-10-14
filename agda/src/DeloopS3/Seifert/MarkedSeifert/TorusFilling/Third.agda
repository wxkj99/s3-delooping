{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Third filling from a marked WComparison, retaining the torus square.
-- WRelJR supplies the comparison used by the TorusFilling entry point.
module DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int as Z using (ℤ; pos)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²)
import DeloopS3.Seifert.MarkedSeifert.WInterface as W
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.HITEquiv
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap using (λ₂)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary

Fill : ℤ → Type₀
Fill e = Pushout λ₂ (row e (pos 1))

abstract
  cong-based : {ℓ ℓ′ : Level} {X : Type ℓ} {Y : Type ℓ′}
    (f : X → Y) {a b : X} (p : a ≡ b) (l : a ≡ a)
    → cong f (based p l) ≡ based (cong f p) (cong f l)
  cong-based f p l = cong-∙ f (sym p ∙ l) p
    ∙ cong (_∙ cong f p) (cong-∙ f (sym p) l)

module FromW (M22e : ℤ → Type₀) (HYPOTHESIS : W.WComparison M22e) where
  open W.WComparison HYPOTHESIS

  WtoKinv : W.W → Kinv
  WtoKinv = relToKinv ∘ W≃RelJR .fst

  bK : T² → Kinv
  bK = WtoKinv ∘ bW

  pK : bK (0C , 0C) ≡ kbase
  pK = cong relToKinv boundary-base

  abstract
    W≃Kinv : W.W ≃ Kinv
    W≃Kinv = WtoKinv , subst isEquiv
      (cong (_∘ W≃RelJR .fst) RelJR-map)
      (compEquiv W≃RelJR RelJR≃Kinv .snd)

    -- Only after the untruncated HIT comparison do we transport this.
    isGroupoidW : isGroupoid W.W
    isGroupoidW = isOfHLevelRespectEquiv 3 (invEquiv W≃Kinv) isGroupoidKinv

    W≃Kinv-map : W≃Kinv .fst ≡ WtoKinv
    W≃Kinv-map = refl

    bK-u : based pK (cong bK uT) ≡ sym (j ∙ (j ∙ sym r))
    bK-u = sym (cong-based relToKinv boundary-base (cong bJR uT))
      ∙ cong (cong relToKinv) boundary-u
      ∙ cong sym (cong-∙ relToKinv W.j (W.j ∙ sym W.r)
          ∙ cong (j ∙_) (cong-∙ relToKinv W.j (sym W.r)))

    bK-v : based pK (cong bK vT) ≡ j ∙ j
    bK-v = sym (cong-based relToKinv boundary-base (cong bJR vT))
      ∙ cong (cong relToKinv) boundary-v ∙ cong-∙ relToKinv W.j W.j

    leftBasis : WtoKinv ∘ bW ∘ σ ≡ λ₂
    leftBasis = MarkedBoundary.leftBasis bK pK bK-u bK-v

    -- First replace W, then reparametrize the entire span by σ.
    -- Both supplied squares are equalities of maps on all of T².
    replaceW : (e : ℤ)
      → Pushout bW (row (pos 1 Z.- e) e) ≃ Pushout bK (row (pos 1 Z.- e) e)
    replaceW e = pushoutEquiv bW (row (pos 1 Z.- e) e)
      bK (row (pos 1 Z.- e) e)
      (idEquiv T²) W≃Kinv (idEquiv C)
      (cong (_∘ bW) W≃Kinv-map) refl

    changeBasis : (e : ℤ) → Fill e ≃ Pushout bK (row (pos 1 Z.- e) e)
    changeBasis e = pushoutEquiv λ₂ (row e (pos 1))
      bK (row (pos 1 Z.- e) e)
      σEquiv (idEquiv Kinv) (idEquiv C)
      (sym leftBasis ∙ cong (bK ∘_) (sym σEquiv-map))
      (sym (rightBasis e) ∙ cong (row (pos 1 Z.- e) e ∘_) (sym σEquiv-map))

    thirdFilling : (e : ℤ) → M22e e ≃ Fill e
    thirdFilling e = compEquiv (thirdStaged e)
      (compEquiv (replaceW e) (invEquiv (changeBasis e)))

    -- The third core is unchanged, not merely taken to a homotopic
    -- unmarked circle. The source is its retained staged representative.
    third-core : (e : ℤ) (t : C)
      → thirdFilling e .fst (invEq (thirdStaged e) (inr t)) ≡ inr t
    third-core e t = cong (invEq (changeBasis e) ∘ replaceW e .fst)
      (secEq (thirdStaged e) (inr t)) ∙ retEq (changeBasis e) (inr t)
