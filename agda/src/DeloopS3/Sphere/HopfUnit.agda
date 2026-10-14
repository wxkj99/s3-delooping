{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Sphere.HopfUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path using (compPathrEquiv)
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration using (fiberEquiv)
open import Cubical.HITs.Join.Base as Join using ()
open import Cubical.HITs.Susp.Base using (north; IsoS³S3)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.HITs.S3 using (S³)
open import Cubical.HITs.Truncation as T
open import Cubical.Homotopy.Connected as Connected
open import Cubical.ZCohomology.GroupStructure using (0ₖ)
open import Cubical.ZCohomology.Properties using (is2ConnectedKn)

open import DeloopS3.Sphere.HopfJoin

-- Projection through the inverse total-space equivalence.
hopfClass : S₊ 2 → K₂
hopfClass = fst ∘ invEq E₀≃S²

hopfClass-base : hopfClass north ≡ 0ₖ 2
hopfClass-base = cong fst (retEq E₀≃S² (0ₖ 2 , Join.inl refl))

hopfClass-fiber : fiber hopfClass (0ₖ 2) ≃ S³
hopfClass-fiber = compEquiv
  (Σ-cong-equiv-fst {B = λ e → fst e ≡ 0ₖ 2} (invEquiv E₀≃S²))
  (compEquiv (fiberEquiv Q₀ (0ₖ 2)) S³'≃S³)

S³-connected : isConnected 4 S³
S³-connected = isConnectedRetractFromIso 4 IsoS³S3 (sphereConnected 3)

-- Extend only the proposition of connectivity, not a chosen fibre equivalence.
hopfClass-connected : isConnectedFun 4 hopfClass
hopfClass-connected = Connected.isConnectedPoint.elim 1
  (is2ConnectedKn 1) (λ _ → isPropIsContr)
  (0ₖ 2 , isConnectedRetractFromIso 4 (equivToIso hopfClass-fiber)
            S³-connected)

-- Uniqueness of reflection, via the library's connectedTruncEquiv.
-- Its forward map computes on generators to hopfClass.
hopfReflectionEquiv : hLevelTrunc 4 (S₊ 2) ≃ K₂
hopfReflectionEquiv = compEquiv
  (connectedTruncEquiv 4 hopfClass hopfClass-connected)
  (truncIdempotent≃ 4 (isOfHLevelTrunc 4))

hopfReflection : (hLevelTrunc 4 (S₊ 2) , ∣ north ∣ₕ) ≃∙ (K₂ , 0ₖ 2)
hopfReflection = hopfReflectionEquiv , hopfClass-base

hopfReflection-unit : equivFun hopfReflectionEquiv ∘ ∣_∣ₕ ≡ hopfClass
hopfReflection-unit = refl

-- The pointed comparison uses exactly hopfClass-base on both sides.
hopfReflection-unit-pointed :
  Path ((S₊ 2 , north) →∙ (K₂ , 0ₖ 2))
    (equivFun hopfReflectionEquiv ∘ ∣_∣ₕ , snd hopfReflection)
    (hopfClass , hopfClass-base)
hopfReflection-unit-pointed = refl

sphereUnitFiber : fiber (∣_∣ₕ {A = S₊ 2} {n = 4}) ∣ north ∣ₕ ≃ S³
sphereUnitFiber = compEquiv
  (Σ-cong-equiv-snd (λ x → compEquiv (congEquiv hopfReflectionEquiv)
                                    (compPathrEquiv hopfClass-base)))
  hopfClass-fiber
