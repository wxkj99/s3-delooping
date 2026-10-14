{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.Final.Localization where

-- Small, opaque functoriality lemmas.  The forward map of L-equiv is the
-- actual RouteB2.L-map, so its unit computation is retained.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import DeloopS3.Local.Base using (F ; L ; η ; local-L)
open import DeloopS3.Local.RouteB2.Common using (L-map)
open import DeloopS3.Local.Unique using (module Unique)

abstract
  L-map-isEquiv : (m : ℕ) (A B : Type) (e : A ≃ B)
    → isEquiv (L-map m {A = A} {B = B} (equivFun e))
  L-map-isEquiv m A B e = isoToIsEquiv (iso forward backward sec ret)
    where
    forward : L m A → L m B
    forward = L-map m {A = A} {B = B} (equivFun e)
    backward : L m B → L m A
    backward = L-map m {A = B} {B = A} (invEq e)
    sec : (y : L m B) → forward (backward y) ≡ y
    sec = Unique.≡onη {F = F m} {X = B} {Y = L m B}
      (local-L m B) (forward ∘ backward) (idfun (L m B))
      (λ b → cong (η {m} {B}) (secEq e b))
    ret : (x : L m A) → backward (forward x) ≡ x
    ret = Unique.≡onη {F = F m} {X = A} {Y = L m A}
      (local-L m A) (backward ∘ forward) (idfun (L m A))
      (λ a → cong (η {m} {A}) (retEq e a))

L-equiv : (m : ℕ) (A B : Type) → A ≃ B → L m A ≃ L m B
L-equiv m A B e = L-map m {A = A} {B = B} (equivFun e) , L-map-isEquiv m A B e
