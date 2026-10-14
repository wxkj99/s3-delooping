{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Fracture.Maps where

-- The canonical arithmetic fracture cospan is defined
-- independently of connectivity, coprimality, and any chosen basepoint.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Nat using (ℕ ; _·_)
open import DeloopS3.Local.Base using (F ; Local ; L ; η ; local-L)
open import DeloopS3.Local.Fracture.Overlap using (product-locality)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations public using (PB)
import Cubical.HITs.Localization.Properties as Loc

abstract
  overlap-local-m : (m n : ℕ) (A : Type) → Local m (L (m · n) A)
  overlap-local-m m n A = fst
    (equivFun (product-locality m n (L (m · n) A)) (local-L (m · n) A))

  overlap-local-n : (m n : ℕ) (A : Type) → Local n (L (m · n) A)
  overlap-local-n m n A = snd
    (equivFun (product-locality m n (L (m · n) A)) (local-L (m · n) A))

ι_m : (m n : ℕ) (A : Type) → L m A → L (m · n) A
ι_m m n A = Loc.rec {F = F m} {X = A} {Y = L (m · n) A}
  (overlap-local-m m n A) (η {m · n} {A})

ι_n : (m n : ℕ) (A : Type) → L n A → L (m · n) A
ι_n m n A = Loc.rec {F = F n} {X = A} {Y = L (m · n) A}
  (overlap-local-n m n A) (η {m · n} {A})

ι_m-β : (m n : ℕ) (A : Type) (a : A)
  → ι_m m n A (η {m} {A} a) ≡ η {m · n} {A} a
ι_m-β m n A a = refl

ι_n-β : (m n : ℕ) (A : Type) (a : A)
  → ι_n m n A (η {n} {A} a) ≡ η {m · n} {A} a
ι_n-β m n A a = refl

fracture-unit : (m n : ℕ) (A : Type)
  → A → PB {A = L m A} {B = L n A} {C = L (m · n) A}
    (ι_m m n A) (ι_n m n A)
fracture-unit m n A a = η {m} {A} a , η {n} {A} a , refl
