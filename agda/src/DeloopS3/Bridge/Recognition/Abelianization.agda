{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Abelianization where

-- Keep the algebraic conversion generic so elaboration never unfolds
-- the implementation of the homotopy-group laws or of HurewiczTheorem.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.AbGroup.Base using (Group→AbGroup)
open import Cubical.Algebra.Group.Abelianization.Base using (Abelianization ; η)
open import Cubical.Algebra.Group.Abelianization.Properties using (AbelianizationIdempotent)

abstract
  abelianization-unit-isEquiv : (G : Group ℓ-zero)
    → ((a b : fst G) → GroupStr._·_ (snd G) a b ≡ GroupStr._·_ (snd G) b a)
    → isEquiv (η {G = G})
  abelianization-unit-isEquiv G comm = isoToIsEquiv
    (fst (AbelianizationIdempotent (Group→AbGroup G comm)))

  remove-abelianization : (G : Group ℓ-zero)
    → ((a b : fst G) → GroupStr._·_ (snd G) a b ≡ GroupStr._·_ (snd G) b a)
    → {H : Type} (h : Abelianization G → H)
    → isEquiv h → isEquiv (h ∘ η)
  remove-abelianization G comm h eh =
    snd (compEquiv (η , abelianization-unit-isEquiv G comm) (h , eh))
