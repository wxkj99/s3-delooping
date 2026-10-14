{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Sphere.HopfJoin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using (_×_; Σ-assoc-Iso; Σ-contractFst)
open import Cubical.Data.Unit using (tt; isContr→≃Unit)
open import Cubical.HITs.Join.Base as Join using (join; S³IsojoinS¹S¹)
open import Cubical.HITs.Join.Properties using (Iso→joinIso)
open import Cubical.HITs.Pushout.Base as PO
  using (Pushout; PushoutSusp; PushoutSusp≃Susp)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Susp.Base using (Susp; north; south; merid)
open import Cubical.HITs.Susp.Properties using (congSuspIso)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.S1 using (S¹; isGroupoidS¹)
open import Cubical.HITs.S3 using (S³)
open import Cubical.HITs.Truncation using (truncIdempotentIso)
open import Cubical.ZCohomology.Base using (coHomK)
open import Cubical.ZCohomology.GroupStructure using (0ₖ)
open import Cubical.ZCohomology.Properties using (Iso-Kn-ΩKn+1)

-- The family Q₀ is a join of based path types; its base fibre is S³.
-- This construction uses neither quaternion multiplication nor the s3sphere library.
K₂ : Type
K₂ = coHomK 2

Q₀ : K₂ → Type
Q₀ h = join (0ₖ 2 ≡ h) (0ₖ 2 ≡ h)

ΩK2IsoS¹ : Iso (Path K₂ (0ₖ 2) (0ₖ 2)) S¹
ΩK2IsoS¹ = compIso (invIso (Iso-Kn-ΩKn+1 1))
                   (truncIdempotentIso 3 isGroupoidS¹)

S³'≃S³ : Q₀ (0ₖ 2) ≃ S³
S³'≃S³ = isoToEquiv
  (compIso (Iso→joinIso ΩK2IsoS¹ ΩK2IsoS¹) (invIso S³IsojoinS¹S¹))

module TotalJoinPushout {ℓ ℓA ℓC : Level}
  (D : Type ℓ) (A : D → Type ℓA) (C : D → Type ℓC) where

  Apex : Type (ℓ-max ℓ (ℓ-max ℓA ℓC))
  Apex = Σ[ d ∈ D ] (A d × C d)

  leftProjection : Apex → Σ D A
  leftProjection (d , x , y) = d , x

  rightProjection : Apex → Σ D C
  rightProjection (d , x , y) = d , y

  totalJoinIsoPushout : Iso (Σ[ d ∈ D ] join (A d) (C d))
                            (Pushout leftProjection rightProjection)
  Iso.fun totalJoinIsoPushout (d , Join.inl x) = PO.inl (d , x)
  Iso.fun totalJoinIsoPushout (d , Join.inr y) = PO.inr (d , y)
  Iso.fun totalJoinIsoPushout (d , Join.push x y i) = PO.push (d , x , y) i
  Iso.inv totalJoinIsoPushout (PO.inl (d , x)) = d , Join.inl x
  Iso.inv totalJoinIsoPushout (PO.inr (d , y)) = d , Join.inr y
  Iso.inv totalJoinIsoPushout (PO.push (d , x , y) i) = d , Join.push x y i
  Iso.sec totalJoinIsoPushout (PO.inl (d , x)) = refl
  Iso.sec totalJoinIsoPushout (PO.inr (d , y)) = refl
  Iso.sec totalJoinIsoPushout (PO.push (d , x , y) i) = refl
  Iso.ret totalJoinIsoPushout (d , Join.inl x) = refl
  Iso.ret totalJoinIsoPushout (d , Join.inr y) = refl
  Iso.ret totalJoinIsoPushout (d , Join.push x y i) = refl

totalPathJoin≃Susp : ∀ {ℓ} (D : Type ℓ) (a c : D)
  → (Σ[ d ∈ D ] join (a ≡ d) (c ≡ d)) ≃ Susp (c ≡ a)
totalPathJoin≃Susp D a c =
  compEquiv (isoToEquiv totalJoinIsoPushout)
    (compEquiv totalPushout≃PushoutSusp PushoutSusp≃Susp)
  where
  open TotalJoinPushout D (λ d → a ≡ d) (λ d → c ≡ d)

  apex≃Path : Apex ≃ (c ≡ a)
  apex≃Path = compEquiv (isoToEquiv (invIso Σ-assoc-Iso))
    (Σ-contractFst {B = λ z → c ≡ fst z} (isContrSingl a))

  totalPushout≃PushoutSusp : Pushout leftProjection rightProjection
                          ≃ PushoutSusp (c ≡ a)
  totalPushout≃PushoutSusp =
    pushoutEquiv leftProjection rightProjection (λ _ → tt) (λ _ → tt)
      apex≃Path (isContr→≃Unit (isContrSingl a))
                (isContr→≃Unit (isContrSingl c)) refl refl

E₀ : Type
E₀ = Σ K₂ Q₀

E₀≃S² : E₀ ≃ S₊ 2
E₀≃S² = compEquiv (totalPathJoin≃Susp K₂ (0ₖ 2) (0ₖ 2))
                   (isoToEquiv (congSuspIso ΩK2IsoS¹))
