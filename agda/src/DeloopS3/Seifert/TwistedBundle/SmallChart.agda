{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Vertex and overlap charts for the coherent quotient span.
-- MarkedSeifert.Final.SmallSpan supplies the span squares and pushout comparison.
module DeloopS3.Seifert.TwistedBundle.SmallChart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Int using (ℤ)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; _+C_; mulC)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Base using (w₁; A; Ksign; λA; fA)
import DeloopS3.Seifert.TwistedBundle.Coherent as D
open D using (Reg; baseQuotient; quotientMap; quotient-agrees)
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Flattening using (module Total)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
open import DeloopS3.Seifert.TwistedBundle.DescentCore

abstract
  ε-natural : (S : B) {T : B} (p : S ≡ T) (y : Reg T) (t : SignC T)
    → ε S (subst Reg (sym p) y) .fst (subst SignC (sym p) t) ≡ ε T y .fst t
  ε-natural S p = evaluation-natural Reg SignC
    (λ T y t → ε T y .fst t) S p

module Filling (e : ℤ) where
  module F = Total e
  open Bundle e using (Mₑ; pₑ)

  leftTotal : F.L ≃ Ksign
  leftTotal = SingletonTotal.equivalence w₁ SignC

  private
    rightReorder : F.R ≃ Σ D.Right (λ q → SignC (fst q))
    rightReorder = isoToEquiv (iso
      (λ { (T , y , t) → (T , y) , t })
      (λ { ((T , y) , t) → T , y , t }) (λ _ → refl) (λ _ → refl))

    discardPointedTorsor : (D.Right × C) ≃ C
    discardPointedTorsor = isoToEquiv (iso snd
      (λ t → fst D.rightContractible , t) (λ _ → refl)
      (λ { (q , t) → ΣPathP (snd D.rightContractible q , refl) }))

  rightTotal : F.R ≃ C
  rightTotal = compEquiv rightReorder
    (compEquiv (Σ-cong-equiv-snd {A = D.Right}
      {B = λ q → SignC (fst q)} {B' = λ _ → C}
      (λ { (T , y) → ε T y })) discardPointedTorsor)

  private
    overlapReorder : F.O ≃ Σ D.Overlap (λ q → SignC (fst q))
    overlapReorder = isoToEquiv (iso
      (λ { (T , (a , y) , t) → (T , a , y) , t })
      (λ { ((T , a , y) , t) → T , (a , y) , t }) (λ _ → refl) (λ _ → refl))

  overlapTotal : F.O ≃ (A × C)
  overlapTotal = compEquiv overlapReorder
    (compEquiv (Σ-cong-equiv-snd {A = D.Overlap}
      {B = λ q → SignC (fst q)} {B' = λ _ → C}
      (λ { (T , a , y) → ε T y }))
      (Σ-cong-equiv-fst {B = λ _ → C} D.overlapChart))

  rowShift : A × C → C
  rowShift (a , t) = t +C mulC e (fA .fst a)


-- In MarkedSeifert.Final.SmallSpan, ε-natural and inverse cancellation give
-- the left square; Action.clutching-seam gives the right square.
