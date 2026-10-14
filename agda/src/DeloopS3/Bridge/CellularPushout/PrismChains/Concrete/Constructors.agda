{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Constructors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.S1.Base using (S¹ ; base)
import Cubical.HITs.SequentialColimit as Colim
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; hasCWskelSphereBouquet/)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ ; hasCWskelSphere)
import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Skeletons as Facts

-- These are levelwise maps, not maps of the finite sets of cells.
module TwoToTwo {a b c d : ℕ}
  (α : FinSphereBouquetMap a b 0) (β : FinSphereBouquetMap c d 0)
  (L : SphereBouquet 1 (Fin b) → SphereBouquet 1 (Fin d))
  (F : cofib α → cofib β)
  (point : L (inl tt) ≡ inl tt)
  (square : (x : SphereBouquet 1 (Fin b)) → inr (L x) ≡ F (inr x)) where

  cellular : cellMap (SphereBouquet/ˢᵏᵉˡ α) (SphereBouquet/ˢᵏᵉˡ β)
  SequenceMap.map cellular zero ()
  SequenceMap.map cellular (suc zero) x = tt
  SequenceMap.map cellular (suc (suc zero)) = L
  SequenceMap.map cellular (suc (suc (suc n))) = F
  SequenceMap.comm cellular zero ()
  SequenceMap.comm cellular (suc zero) x =
    Facts.Bouquet.vertex β tt ∙ sym point
      ∙ cong L (sym (Facts.Bouquet.vertex α x))
  SequenceMap.comm cellular (suc (suc zero)) x =
    Facts.Bouquet.edge β (L x) ∙ square x
      ∙ cong F (sym (Facts.Bouquet.edge α x))
  SequenceMap.comm cellular (suc (suc (suc n))) x =
    Facts.Bouquet.stable β n (F x)
      ∙ cong F (sym (Facts.Bouquet.stable α n x))

  abstract
    realise-top : (x : cofib α)
      → realiseCellMap cellular (fst (snd (hasCWskelSphereBouquet/ α)) x)
       ≡ fst (snd (hasCWskelSphereBouquet/ β)) (F x)
    realise-top x = refl

module TwoToCircle {a b : ℕ} (α : FinSphereBouquetMap a b 0)
  (F : cofib α → S¹) (point : F (inr (inl tt)) ≡ base) where

  cellular : cellMap (SphereBouquet/ˢᵏᵉˡ α) (Sˢᵏᵉˡ 1)
  SequenceMap.map cellular zero ()
  SequenceMap.map cellular (suc zero) x = tt
  SequenceMap.map cellular (suc (suc zero)) x = F (inr x)
  SequenceMap.map cellular (suc (suc (suc n))) = F
  SequenceMap.comm cellular zero ()
  SequenceMap.comm cellular (suc zero) x =
    Facts.Circle.vertex tt ∙ sym point
      ∙ cong (F ∘ inr) (sym (Facts.Bouquet.vertex α x))
  SequenceMap.comm cellular (suc (suc zero)) x =
    Facts.Circle.stable₂ (F (inr x))
      ∙ cong F (sym (Facts.Bouquet.edge α x))
  SequenceMap.comm cellular (suc (suc (suc n))) x =
    Facts.Circle.stable n (F x)
      ∙ cong F (sym (Facts.Bouquet.stable α n x))

  abstract
    realise-top : (x : cofib α)
      → realiseCellMap cellular (fst (snd (hasCWskelSphereBouquet/ α)) x)
       ≡ fst (snd (hasCWskelSphere 1)) (F x)
    realise-top x = sym (Colim.push {n = 2} (F x))
