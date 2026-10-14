{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusIntegerCylinder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv-snd)
import Cubical.Data.Sum as Sum
open import Cubical.HITs.Susp.Base using (Susp ; north ; south ; merid ; S¹IsoSuspBool)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr ; push)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.ComponentHomology.Circle using (C-finite ; circleCW)
open import DeloopS3.Bridge.ComponentHomology.Finite using (sum-finite₁)
open import DeloopS3.Move.CancelMinimal using (C ; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Cert.Interpret.Realization as R

module Cylinder (X : Type) where
  fold : X Sum.⊎ X → X
  fold (Sum.inl x) = x
  fold (Sum.inr x) = x

  Total : Type
  Total = Pushout fold fold

  chart : Iso (X × Susp Bool) Total
  Iso.fun chart (x , north) = inl x
  Iso.fun chart (x , south) = inr x
  Iso.fun chart (x , merid true i) = push (Sum.inl x) i
  Iso.fun chart (x , merid false i) = push (Sum.inr x) i
  Iso.inv chart (inl x) = x , north
  Iso.inv chart (inr x) = x , south
  Iso.inv chart (push (Sum.inl x) i) = x , merid true i
  Iso.inv chart (push (Sum.inr x) i) = x , merid false i
  Iso.sec chart (inl x) = refl
  Iso.sec chart (inr x) = refl
  Iso.sec chart (push (Sum.inl x) i) = refl
  Iso.sec chart (push (Sum.inr x) i) = refl
  Iso.ret chart (x , north) = refl
  Iso.ret chart (x , south) = refl
  Iso.ret chart (x , merid true i) = refl
  Iso.ret chart (x , merid false i) = refl

  span : R.Span ℓ-zero ℓ-zero ℓ-zero
  R.Span.O span = X Sum.⊎ X
  R.Span.L span = X
  R.Span.R span = X
  R.Span.left span = fold
  R.Span.right span = fold

  endomap : (X → X) → Map.ContinuousSpanMap span span
  Map.overlapMap (endomap f) = Sum.map f f
  Map.leftMap (endomap f) = f
  Map.rightMap (endomap f) = f
  Map.leftSquare (endomap f) (Sum.inl x) = refl
  Map.leftSquare (endomap f) (Sum.inr x) = refl
  Map.rightSquare (endomap f) (Sum.inl x) = refl
  Map.rightSquare (endomap f) (Sum.inr x) = refl

  abstract
    chart-natural : (f : X → X) (z : X × Susp Bool)
      → Map.totalMap (endomap f) (Iso.fun chart z)
        ≡ Iso.fun chart (f (fst z) , snd z)
    chart-natural f (x , north) = refl
    chart-natural f (x , south) = refl
    chart-natural f (x , merid true i) j =
      doubleCompPath-filler refl (push (Sum.inl (f x))) refl (~ j) i
    chart-natural f (x , merid false i) j =
      doubleCompPath-filler refl (push (Sum.inr (f x))) refl (~ j) i

module CylinderC = Cylinder C

circle-susp : C ≃ Susp Bool
circle-susp = compEquiv (invEquiv S¹≃C) (isoToEquiv S¹IsoSuspBool)

torus-cylinder : T² ≃ CylinderC.Total
torus-cylinder = compEquiv (Σ-cong-equiv-snd (λ _ → circle-susp))
  (isoToEquiv CylinderC.chart)

overlap-finite : Finite≤ 1 (C Sum.⊎ C)
overlap-finite = sum-finite₁ C-finite C-finite

overlapCW cylinderCW : CW₀
overlapCW = (C Sum.⊎ C) , finite≤→isCW overlap-finite
cylinderCW = CylinderC.Total , finite≤→isCW
  (pushout-finite≤ CylinderC.fold CylinderC.fold 1 1 1
    overlap-finite C-finite C-finite)

abstract
  torus-cylinder-natural : (f : C → C)
    → Map.totalMap (CylinderC.endomap f) ∘ equivFun torus-cylinder
      ≡ equivFun torus-cylinder ∘ (λ (u , t) → f u , t)
  torus-cylinder-natural f = funExt λ (u , t) →
    CylinderC.chart-natural f (u , equivFun circle-susp t)
