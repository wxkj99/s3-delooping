{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv-snd)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Susp.Base using
  (Susp ; north ; south ; merid ; S¹IsoSuspBool ; BoolIsoSusp⊥)
open import Cubical.HITs.Susp.Properties using (congSuspIso)
open import Cubical.HITs.Pushout using
  (Pushout ; inl ; inr ; push ; PushoutEmptyDomainIso)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.CW.Base using (finCWskel)
open import Cubical.CW.Instances.Empty using (finCWskel⊥ ; hasCWskel⊥)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.ComponentHomology.Circle
open import DeloopS3.Move.CancelMinimal using (C ; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition using (P ; Core ; wedgeLeg)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
import DeloopS3.Seifert.TwistedBundle.Base as RP
open import Cubical.HITs.RPn.Base using (RP1≡S1)

private
  emptySkel : finCWskel ℓ-zero 1
  emptySkel = fst finCWskel⊥ , fst (snd finCWskel⊥) ,
    λ k → snd (snd finCWskel⊥) k

  empty-finite : Finite≤ 0 ⊥
  empty-finite = PT.∣ emptySkel , snd hasCWskel⊥ ∣₁

abstract
  graph-finite : Finite≤ 1 P
  graph-finite = pushout-finite≤ wedgeLeg wedgeLeg 0 1 1
    unit-finite≤ C-finite C-finite

  sum-finite₁ : {X Y : Type} → Finite≤ 1 X → Finite≤ 1 Y
    → Finite≤ 1 (X Sum.⊎ Y)
  sum-finite₁ fx fy = finite-equiv (invEquiv (isoToEquiv PushoutEmptyDomainIso))
    (pushout-finite≤ (λ ()) (λ ()) 0 1 1 empty-finite fx fy)

private
  boolProductIso : (X : Type) → Iso (Bool × X) (X Sum.⊎ X)
  Iso.fun (boolProductIso X) (false , x) = Sum.inl x
  Iso.fun (boolProductIso X) (true , x) = Sum.inr x
  Iso.inv (boolProductIso X) (Sum.inl x) = false , x
  Iso.inv (boolProductIso X) (Sum.inr x) = true , x
  Iso.sec (boolProductIso X) (Sum.inl x) = refl
  Iso.sec (boolProductIso X) (Sum.inr x) = refl
  Iso.ret (boolProductIso X) (false , x) = refl
  Iso.ret (boolProductIso X) (true , x) = refl

  -- A concrete cylinder chart, not a general product-cell theorem.
  cylinderIso : (X : Type) → Iso (X × Susp Bool)
    (Pushout {A = Bool × X} snd snd)
  Iso.fun (cylinderIso X) (x , north) = inl x
  Iso.fun (cylinderIso X) (x , south) = inr x
  Iso.fun (cylinderIso X) (x , merid b i) = push (b , x) i
  Iso.inv (cylinderIso X) (inl x) = x , north
  Iso.inv (cylinderIso X) (inr x) = x , south
  Iso.inv (cylinderIso X) (push (b , x) i) = x , merid b i
  Iso.sec (cylinderIso X) (inl x) = refl
  Iso.sec (cylinderIso X) (inr x) = refl
  Iso.sec (cylinderIso X) (push (b , x) i) = refl
  Iso.ret (cylinderIso X) (x , north) = refl
  Iso.ret (cylinderIso X) (x , south) = refl
  Iso.ret (cylinderIso X) (x , merid b i) = refl

abstract
  circle-product-finite₂ : {X : Type} → Finite≤ 1 X → Finite≤ 2 (X × C)
  circle-product-finite₂ {X} fx = finite-equiv
    (Σ-cong-equiv-snd (λ _ → compEquiv (invEquiv S¹≃C) (isoToEquiv S¹IsoSuspBool)))
    (finite-equiv (isoToEquiv (cylinderIso X))
      (pushout-finite≤ snd snd 1 1 1
        (finite-equiv (isoToEquiv (boolProductIso X)) (sum-finite₁ fx fx)) fx fx))

  torus-finite : Finite≤ 2 T²
  torus-finite = circle-product-finite₂ C-finite

  graph×circle-finite : Finite≤ 2 Core
  graph×circle-finite = circle-product-finite₂ graph-finite

  RP¹-circle : RP.R ≃ S¹
  RP¹-circle = compEquiv (pathToEquiv RP1≡S1)
    (invEquiv (isoToEquiv (compIso S¹IsoSuspBool (congSuspIso BoolIsoSusp⊥))))

  RP¹-finite : Finite≤ 1 RP.R
  RP¹-finite = finite-equiv RP¹-circle S¹-finite

  RP-total-finite : Finite≤ 1 RP.A
  RP-total-finite = finite-equiv RP.fA C-finite

  RP²-finite : Finite≤ 2 RP²
  RP²-finite = pushout-finite≤ RP.pr₁ RP.cap 1 1 0
    RP-total-finite RP¹-finite unit-finite≤

graphCW torusCW graph×circleCW RP²CW : CW₀
graphCW = P , finite≤→isCW graph-finite
torusCW = T² , finite≤→isCW torus-finite
graph×circleCW = Core , finite≤→isCW graph×circle-finite
RP²CW = RP² , finite≤→isCW RP²-finite
