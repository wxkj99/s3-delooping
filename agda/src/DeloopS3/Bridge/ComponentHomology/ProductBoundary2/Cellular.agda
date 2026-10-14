{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Cellular where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Pushout using (inl)
open import Cubical.HITs.SphereBouquet using (FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree ; bouquetDegreeSusp)
open import Cubical.Algebra.Group.MorphismProperties using (trivGroupHom ; GroupHom≡)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (agreeOnℤFinGenerator→≡)
open import Cubical.CW.ChainComplex using (∂)
open import Cubical.CW.Instances.SphereBouquetMap using (SphereBouquet/ˢᵏᵉˡ)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (bouquetSusp→Charac ; inKerGenerator)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Degree

abstract
  cofibre-square-degree : {m k : ℕ} (f : FinSphereBouquetMap m k 0)
    → f (inl tt) ≡ inl tt
    → ∂ (SphereBouquet/ˢᵏᵉˡ f) 1 ≡ bouquetDegree f
  cofibre-square-degree f point =
    cong bouquetDegree (bouquetSusp→Charac f (λ _ → pos 0) (λ _ → pos 0) point refl refl)
    ∙ sym (bouquetDegreeSusp f)

module ProductDifferentials (n : ℕ) where
  open RoseProduct n
  open ProductNull n

  abstract
    edge-differential-zero : ∂ skeleton 0 ≡ trivGroupHom
    edge-differential-zero = agreeOnℤFinGenerator→≡ (inKerGenerator attaching)

    square-differential-zero : ∂ skeleton 1 ≡ trivGroupHom
    square-differential-zero = cofibre-square-degree attaching attaching-point
      ∙ attaching-degree-zero

    above-differential-zero : ∂ skeleton 2 ≡ trivGroupHom
    above-differential-zero = GroupHom≡ (funExt λ r → funExt λ k → refl)
