{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductCells where

-- A finite rose crossed with one circle, via the Whitehead
-- attaching pushout.  This supplies the actual (1,n+1,n) cell structure;
-- it is not an assumed product formula for homology.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool ; true)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Susp using
  (Susp ; north ; S¹IsoSuspBool ; Susp≃joinBool)
open import Cubical.HITs.Join using (join)
open import Cubical.HITs.Pushout using
  (cofib ; inl ; inr ; push ; pushoutEquiv ; symPushout)
open import Cubical.HITs.Wedge using (_⋁_ ; Iso-⋁genFinSuc-⋁genFin⋁)
open import Cubical.HITs.SphereBouquet using
  (SphereBouquet ; FinSphereBouquetMap ; sphereBouquet≃Susp)
open import DeloopS3.Compat.Whitehead using
  (joinTo⋁ ; Iso-Susp×Susp-cofibJoinTo⋁)
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; hasCWskelSphereBouquet/)
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre using (one-equiv)
open import DeloopS3.Bridge.ComponentHomology.Graph using (graph-bouquet)
open import DeloopS3.Move.CancelMinimal using (T²)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition using (Core)

module RoseProduct (n : ℕ) where
  Vertices : Type
  Vertices = SphereBouquet 0 (Fin n)

  Rose : Type
  Rose = SphereBouquet 1 (Fin n)

  Wedge : Type
  Wedge = (Susp Vertices , north) ⋁ (Susp Bool , north)

  W : join Vertices Bool → Wedge
  W = joinTo⋁ {A = Vertices , inl tt} {B = Bool , true}

  suspension-chart : Susp Vertices ≃ Rose
  suspension-chart = sphereBouquet≃Susp

  circle-chart : Susp Bool ≃ S¹
  circle-chart = invEquiv (isoToEquiv S¹IsoSuspBool)

  source-chart : Rose ≃ join Vertices Bool
  source-chart = compEquiv (invEquiv suspension-chart) Susp≃joinBool

  target-chart : Wedge ≃ SphereBouquet 1 (Fin (suc n))
  target-chart = compEquiv
    (pushoutEquiv (λ _ → north) (λ _ → north)
      (λ _ → inl tt) (λ _ → base) (idEquiv Unit)
      suspension-chart circle-chart refl refl)
    (invEquiv (isoToEquiv Iso-⋁genFinSuc-⋁genFin⋁))

  attaching : FinSphereBouquetMap n (suc n) 0
  attaching = fst target-chart ∘ W ∘ fst source-chart

  abstract
    attaching-point : attaching (inl tt) ≡ inl tt
    attaching-point = refl

    product-cofibre : (Rose × S¹) ≃ cofib attaching
    product-cofibre = compEquiv
      (Σ-cong-equiv-fst {B = λ _ → S¹} (invEquiv suspension-chart))
      (compEquiv (Σ-cong-equiv-snd (λ _ → invEquiv circle-chart))
        (compEquiv
          (isoToEquiv (Iso-Susp×Susp-cofibJoinTo⋁ Vertices Bool (inl tt) true))
          (compEquiv (symPushout W (λ _ → tt))
            (pushoutEquiv (λ _ → tt) W (λ _ → tt) attaching
              (invEquiv source-chart) (idEquiv Unit) target-chart refl
              (funExt λ x → cong (fst target-chart ∘ W)
                (sym (secEq source-chart x)))))))

    product-cofibre-unfold : Path ((Rose × S¹) ≃ cofib attaching) product-cofibre
      (compEquiv
        (Σ-cong-equiv-fst {B = λ _ → S¹} (invEquiv suspension-chart))
        (compEquiv (Σ-cong-equiv-snd (λ _ → invEquiv circle-chart))
          (compEquiv
            (isoToEquiv (Iso-Susp×Susp-cofibJoinTo⋁ Vertices Bool (inl tt) true))
            (compEquiv (symPushout W (λ _ → tt))
              (pushoutEquiv (λ _ → tt) W (λ _ → tt) attaching
                (invEquiv source-chart) (idEquiv Unit) target-chart refl
                (funExt λ x → cong (fst target-chart ∘ W)
                  (sym (secEq source-chart x))))))))
    product-cofibre-unfold = refl

  skeleton : CWskel ℓ-zero
  skeleton = SphereBouquet/ˢᵏᵉˡ attaching

  has-skeleton : hasCWskel (Rose × S¹)
  has-skeleton = skeleton , compEquiv product-cofibre
    (snd (hasCWskelSphereBouquet/ attaching))

  abstract
    cells₀ : snd skeleton .fst 0 ≡ 1
    cells₀ = refl

    cells₁ : snd skeleton .fst 1 ≡ suc n
    cells₁ = refl

    cells₂ : snd skeleton .fst 2 ≡ n
    cells₂ = refl

private
  torus-rose : T² ≃ (RoseProduct.Rose 1 × S¹)
  torus-rose = compEquiv
    (Σ-cong-equiv-fst {B = λ _ → _} (compEquiv (invEquiv S¹≃C) (invEquiv one-equiv)))
    (Σ-cong-equiv-snd (λ _ → invEquiv S¹≃C))

  core-rose : Core ≃ (RoseProduct.Rose 2 × S¹)
  core-rose = compEquiv
    (Σ-cong-equiv-fst {B = λ _ → _} (invEquiv graph-bouquet))
    (Σ-cong-equiv-snd (λ _ → invEquiv S¹≃C))

torusSkel graph×circleSkel : CWskel ℓ-zero
torusSkel = RoseProduct.skeleton 1
graph×circleSkel = RoseProduct.skeleton 2

torus-skeleton : hasCWskel T²
torus-skeleton = torusSkel , compEquiv torus-rose (snd (RoseProduct.has-skeleton 1))

graph×circle-skeleton : hasCWskel Core
graph×circle-skeleton = graph×circleSkel , compEquiv core-rose (snd (RoseProduct.has-skeleton 2))
