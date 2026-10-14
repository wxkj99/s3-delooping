{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Skeletons where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Fin using (Fin)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.CW.Base using (CWskel ; CW↪)
open import Cubical.CW.Instances.SphereBouquetMap using (SphereBouquet/ˢᵏᵉˡ)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ)
open import Cubical.HITs.S1.Base using (S¹ ; base)

module Bouquet {a b : ℕ} (α : FinSphereBouquetMap a b 0) where
  S : CWskel ℓ-zero
  S = SphereBouquet/ˢᵏᵉˡ α

  abstract
    vertex : (x : Unit) → CW↪ S 1 x ≡ inl tt
    vertex x = refl

    edge : (x : SphereBouquet 1 (Fin b)) → CW↪ S 2 x ≡ inr x
    edge x = refl

    stable : (n : ℕ) (x : cofib α) → CW↪ S (suc (suc (suc n))) x ≡ x
    stable n x = refl

module Circle where
  S : CWskel ℓ-zero
  S = Sˢᵏᵉˡ 1

  abstract
    vertex : (x : Unit) → CW↪ S 1 x ≡ base
    vertex x = refl

    stable₂ : (x : S¹) → CW↪ S 2 x ≡ x
    stable₂ x = refl

    stable : (n : ℕ) (x : S¹) → CW↪ S (suc (suc (suc n))) x ≡ x
    stable n x = refl
