{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.HurewiczBase where

-- The Hurewicz equivalence with an opaque abelianization adapter.
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.Recognition.Abelianization
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Homotopy.Group.Base using (π'Gr ; π'-comm)
open import Cubical.Homotopy.Connected
open import Cubical.CW.HurewiczTheorem using
  (HurewiczTheorem ; HurewiczHomAb ; HurewiczMap)

-- The opaque generic algebra adapter prevents elaboration from expanding
-- the entire homotopy-group structure in the abelianization comparison.
abstract
  hurewicz-isEquiv : (X : CW₀) (n : ℕ)
    (conn : isConnected (3 + n) (fst X)) (x : fst X)
    → isEquiv (HurewiczMap {n = suc n} X x)
  hurewicz-isEquiv X n conn x = remove-abelianization
    (π'Gr (suc n) (fst X , x)) (π'-comm n {A = fst X , x})
    (fst (HurewiczHomAb X x (isConnectedSubtr' (suc n) 2 conn) (suc n)))
    (HurewiczTheorem (suc n) X conn x)

hurewicz-equiv : (X : CW₀) (n : ℕ)
  (conn : isConnected (3 + n) (fst X)) (x : fst X)
  → fst (π'Gr (suc n) (fst X , x)) ≃ fst (H̃ᶜʷ X (2 + n))
hurewicz-equiv X n conn x = HurewiczMap {n = suc n} X x , hurewicz-isEquiv X n conn x
