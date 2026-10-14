{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets.Finite where

-- Proof-free sheet-coordinate searches with reflected inverse equations.
-- Defaults only make search total; the reflected equations validate hits.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; _and_; if_then_else_)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; toℕ; toℕ-injective)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.FiniteReflection
import DeloopS3.Cert.Perm as P

search : {A : Type₀} → (A → Bool) → List A → A → A
search p [] d = d
search p (x ∷ xs) d = if p x then x else search p xs d

finEq : {n : ℕ} → Fin n → Fin n → Bool
finEq x y = toℕ x ≡ᵇ toℕ y

finEq-sound : {n : ℕ} (x y : Fin n) → finEq x y ≡ true → x ≡ y
finEq-sound x y p = toℕ-injective (natEq-sound _ _ p)

module Lookup (nh ns ng : ℕ)
  (hTable : Fin nh → P.Table) (rTable : Fin ns → P.Table)
  (gTable : Fin ng → P.Table)
  (h₀ : Fin nh) (s₀ : Fin ns) (g₀ : Fin ng) where

  Pair : Type₀
  Pair = Fin nh × Fin ns

  productTable : Pair → P.Table
  productTable (h , i) = P.compose (hTable h) (rTable i)

  pairs : List Pair
  pairs = P.concatMap (λ h → sample ns (λ i → h , i)) (sample nh (λ h → h))

  findGroup : P.Table → Fin ng
  findGroup t = search (λ g → P.tableEq (gTable g) t) (sample ng (λ g → g)) g₀

  forward : Pair → Fin ng
  forward x = findGroup (productTable x)

  backward : Fin ng → Pair
  backward g = search (λ x → P.tableEq (productTable x) (gTable g)) pairs (h₀ , s₀)

  retH retS hitB retAt : Pair → Bool
  retH x = finEq (backward (forward x) .fst) (x .fst)
  retS x = finEq (backward (forward x) .snd) (x .snd)
  hitB x = P.tableEq (gTable (forward x)) (productTable x)
  retAt x = retH x and (retS x and hitB x)

  retCheck secCheck : Bool
  retCheck = allFin (λ h → allFin (λ i → retAt (h , i)))
  secCheck = allFin (λ g → finEq (forward (backward g)) g)

  module Checked (retOK : retCheck ≡ true) (secOK : secCheck ≡ true) where
    abstract
      ret-at : (x : Pair) → retAt x ≡ true
      ret-at (h , i) = allFin-sound (λ i → retAt (h , i))
        (allFin-sound (λ h → allFin (λ i → retAt (h , i))) retOK h) i

      forward-table : (x : Pair) → gTable (forward x) ≡ productTable x
      forward-table x = tableEq-sound _ _
        (and-right {a = retS x} {b = hitB x}
          (and-right {a = retH x} {b = retS x and hitB x} (ret-at x)))

      ret : (x : Pair) → backward (forward x) ≡ x
      ret x = cong₂ _,_
        (finEq-sound _ _ (and-left {a = retH x} {b = retS x and hitB x} (ret-at x)))
        (finEq-sound _ _ (and-left {a = retS x} {b = hitB x}
          (and-right {a = retH x} {b = retS x and hitB x} (ret-at x))))

      sec : (g : Fin ng) → forward (backward g) ≡ g
      sec g = finEq-sound _ _ (allFin-sound (λ g → finEq (forward (backward g)) g) secOK g)

    equivalence : Pair ≃ Fin ng
    equivalence = isoToEquiv (iso forward backward sec ret)
