{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.FiniteReflection where

-- Finite exhaustive checks with their reflection lemmas.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_; znots; injSuc)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; _or_; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ; toℕ-injective)
open import Cubical.Data.Empty as Empty using (⊥)
open import DeloopS3.Groups.TablePermutation
import DeloopS3.Cert.Perm as P

private variable A : Type

sample : (n : ℕ) → (Fin n → A) → List A
sample zero f = []
sample (suc n) f = f fzero ∷ sample n (λ i → f (fsuc i))

sample-length : (n : ℕ) (f : Fin n → A) → P.length (sample n f) ≡ n
sample-length zero f = refl
sample-length (suc n) f = cong suc (sample-length n (λ i → f (fsuc i)))

sample-nth : {n : ℕ} (d : A) (f : Fin n → A) (i : Fin n)
  → P.nth d (sample n f) (toℕ i) ≡ f i
sample-nth {n = suc n} d f fzero = refl
sample-nth {n = suc n} d f (fsuc i) = sample-nth d (λ i → f (fsuc i)) i

sample-member : {n : ℕ} (f : Fin n → A) (i : Fin n) → f i ∈ sample n f
sample-member {n = suc n} f fzero = here
sample-member {n = suc n} f (fsuc i) = there (sample-member (λ i → f (fsuc i)) i)

sample-member⁻ : {n : ℕ} (f : Fin n → A) {x : A} → x ∈ sample n f
  → Σ[ i ∈ Fin n ] f i ≡ x
sample-member⁻ {n = suc n} f here = fzero , refl
sample-member⁻ {n = suc n} f (there m) =
  let w = sample-member⁻ (λ i → f (fsuc i)) m in fsuc (w .fst) , w .snd

all-complete : (f : A → Bool) (xs : List A)
  → ({x : A} → x ∈ xs → f x ≡ true) → P.all f xs ≡ true
all-complete f [] p = refl
all-complete f (x ∷ xs) p = cong₂ _and_ (p here) (all-complete f xs (λ m → p (there m)))

not-member : (eq : A → A → Bool) → ((x y : A) → eq x y ≡ true → x ≡ y)
  → (x : A) (xs : List A) → (x ∈ xs → ⊥) → not (P.member eq x xs) ≡ true
not-member eq sound x xs no with P.member eq x xs | member-sound eq sound x xs
... | false | w = refl
... | true | w = Empty.rec (no (w refl))

unique-sample : (eq : A → A → Bool) → ((x y : A) → eq x y ≡ true → x ≡ y)
  → (n : ℕ) (f : Fin n → A) → ({i j : Fin n} → f i ≡ f j → i ≡ j)
  → P.unique eq (sample n f) ≡ true
unique-sample eq sound zero f inj = refl
unique-sample eq sound (suc n) f inj = cong₂ _and_
  (not-member eq sound (f fzero) (sample n (λ i → f (fsuc i)))
    (λ m → let w = sample-member⁻ (λ i → f (fsuc i)) m
           in znots (cong toℕ (inj (sym (w .snd))))))
  (unique-sample eq sound n (λ i → f (fsuc i))
    (λ p → toℕ-injective (injSuc (cong toℕ (inj p)))))

natEq-complete : {x y : ℕ} → x ≡ y → (x ≡ᵇ y) ≡ true
natEq-complete {x} p = cong (x ≡ᵇ_) (sym p) ∙ natEq-refl x

tableOf : {n : ℕ} → (Fin n → Fin n) → P.Table
tableOf {n} f = sample n (λ i → toℕ (f i))

tableOf-valid : {n : ℕ} (e : Fin n ≃ Fin n) → P.isPerm n (tableOf (e .fst)) ≡ true
tableOf-valid {n} e = cong₂ _and_
  (natEq-complete (sample-length n f))
  (cong₂ _and_ (unique-sample _≡ᵇ_ natEq-sound n f inj)
    (cong₂ _and_
      (all-complete (λ x → P.member _≡ᵇ_ x (P.range n)) (tableOf (e .fst)) into)
      (all-complete (λ x → P.member _≡ᵇ_ x (tableOf (e .fst))) (P.range n) onto)))
  where
  f = λ i → toℕ (e .fst i)
  inj : {i j : Fin n} → f i ≡ f j → i ≡ j
  inj {i} {j} p = sym (retEq e i) ∙ cong (invEq e) (toℕ-injective p) ∙ retEq e j
  into : {x : ℕ} → x ∈ tableOf (e .fst) → P.member _≡ᵇ_ x (P.range n) ≡ true
  into m = let w = sample-member⁻ f m in member-complete _≡ᵇ_ natEq-refl
    (subst (_∈ P.range n) (w .snd) (range-member (e .fst (w .fst))))
  onto : {x : ℕ} → x ∈ P.range n → P.member _≡ᵇ_ x (tableOf (e .fst)) ≡ true
  onto {x} m = let w = range-bound n x m in member-complete _≡ᵇ_ natEq-refl
    (subst (_∈ tableOf (e .fst)) (cong toℕ (secEq e (w .fst)) ∙ w .snd)
      (sample-member f (invEq e (w .fst))))

tableOf-sound : {n : ℕ} (e : Fin n ≃ Fin n)
  → tablePermutation {t = tableOf (e .fst)} (tableOf-valid e) ≡ e
tableOf-sound e = equivEq (funExt λ i → toℕ-injective
  (tablePermutation-value {t = tableOf (e .fst)} (tableOf-valid e) i
   ∙ sample-nth (P.length (tableOf (e .fst))) (λ i → toℕ (e .fst i)) i))

-- This checker ranges over n^k bounded tables, not unchecked arbitrary
-- functions or a postulated list of permutations.
allTables : (n k : ℕ) → (P.Table → Bool) → Bool
allTables n zero f = f []
allTables n (suc k) f = P.all (λ x → allTables n k (λ xs → f (x ∷ xs))) (P.range n)

allTables-sound : (n k : ℕ) (f : P.Table → Bool) → allTables n k f ≡ true
  → (g : Fin k → Fin n) → f (sample k (λ i → toℕ (g i))) ≡ true
allTables-sound n zero f v g = v
allTables-sound n (suc k) f v g = allTables-sound n k (λ xs → f (toℕ (g fzero) ∷ xs))
  (all-sound (λ x → allTables n k (λ xs → f (x ∷ xs))) v (range-member (g fzero)))
  (λ i → g (fsuc i))

allFin : {n : ℕ} → (Fin n → Bool) → Bool
allFin {zero} f = true
allFin {suc n} f = f fzero and allFin (λ i → f (fsuc i))

allFin-sound : {n : ℕ} (f : Fin n → Bool) → allFin f ≡ true → (i : Fin n) → f i ≡ true
allFin-sound {suc n} f p fzero = and-left p
allFin-sound {suc n} f p (fsuc i) = allFin-sound (λ i → f (fsuc i)) (and-right p) i

open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import DeloopS3.Groups.Enumerated using (certificate-cong)

-- Encode a SymGroup element in certificate convention, so encode/decode
-- both invert; their roundtrip never silently reverses a marked word.
certificateTable : {n : ℕ} → FinSymGroup n .fst → P.Table
certificateTable e = tableOf (invEq e)

certificateTable-valid : {n : ℕ} (e : FinSymGroup n .fst) → P.isPerm n (certificateTable e) ≡ true
certificateTable-valid e = tableOf-valid (invEquiv e)

certificateTable-sound : {n : ℕ} (e : FinSymGroup n .fst)
  (v : P.isPerm n (certificateTable e) ≡ true)
  → certificatePermutation {t = certificateTable e} v ≡ e
certificateTable-sound {n} e v =
  certificate-cong (certificateTable e) (certificateTable e) v (certificateTable-valid e) refl
  ∙ cong invEquiv (tableOf-sound (invEquiv e)) ∙ GroupTheory.invInv (FinSymGroup n) e

tableOf-roundtrip : {n : ℕ} (t : P.Table) (v : P.isPerm n t ≡ true)
  → tableOf (tablePermutation {t = t} v .fst) ≡ t
tableOf-roundtrip {n} t v = nth-ext n 0 (P.length t) (tableOf (tablePermutation {t = t} v .fst)) t
  (sample-length n _) (Valid.len {t = t} v)
  (λ i → sample-nth _ _ i ∙ tablePermutation-value {t = t} v i)

certificateTable-roundtrip : {n : ℕ} (t : P.Table) (v : P.isPerm n t ≡ true)
  → certificateTable (certificatePermutation {t = t} v) ≡ t
certificateTable-roundtrip {n} t v =
  cong (λ e → tableOf (e .fst)) (GroupTheory.invInv (FinSymGroup n) (tablePermutation {t = t} v))
  ∙ tableOf-roundtrip t v

open import Cubical.Data.Bool using (if_then_else_)

filter-member : (f : ℕ → Bool) {x : ℕ} {xs : P.Table}
  → f x ≡ true → x ∈ xs → x ∈ P.filter f xs
filter-member f {x} {xs = x ∷ xs} p here = subst (λ b → x ∈ (if b then x ∷ P.filter f xs else P.filter f xs)) (sym p) here
filter-member f {xs = y ∷ ys} p (there m) with f y
... | true = there (filter-member f p m)
... | false = filter-member f p m

not-natEq : (x y : ℕ) → (x ≡ y → ⊥) → not (x ≡ᵇ y) ≡ true
not-natEq x y no with x ≡ᵇ y | natEq-sound x y
... | false | s = refl
... | true | s = Empty.rec (no (s refl))

-- Pruning already chosen values gives n! leaves instead of n^n. The
-- completeness proof below, not a trusted generator, justifies the pruning.
allDistinctTables : P.Table → ℕ → (P.Table → Bool) → Bool
allDistinctTables pool zero f = f []
allDistinctTables pool (suc k) f = P.all (λ x → allDistinctTables
  (P.filter (λ y → not (y ≡ᵇ x)) pool) k (λ xs → f (x ∷ xs))) pool

allDistinctTables-sound : (pool : P.Table) (k : ℕ) (f : P.Table → Bool)
  → allDistinctTables pool k f ≡ true → (g : Fin k → ℕ)
  → ({i j : Fin k} → g i ≡ g j → i ≡ j)
  → ((i : Fin k) → g i ∈ pool) → f (sample k g) ≡ true
allDistinctTables-sound pool zero f v g inj mem = v
allDistinctTables-sound pool (suc k) f v g inj mem =
  allDistinctTables-sound (P.filter (λ y → not (y ≡ᵇ g fzero)) pool) k
    (λ xs → f (g fzero ∷ xs))
    (all-sound (λ x → allDistinctTables (P.filter (λ y → not (y ≡ᵇ x)) pool) k (λ xs → f (x ∷ xs))) v (mem fzero))
    (λ i → g (fsuc i))
    (λ p → toℕ-injective (injSuc (cong toℕ (inj p))))
    (λ i → filter-member (λ y → not (y ≡ᵇ g fzero))
      (not-natEq (g (fsuc i)) (g fzero) (λ p → znots (cong toℕ (inj (sym p))))) (mem (fsuc i)))

allPermutations : (n : ℕ) → (P.Table → Bool) → Bool
allPermutations n = allDistinctTables (P.range n) n

allPermutations-sound : (n : ℕ) (f : P.Table → Bool) → allPermutations n f ≡ true
  → (e : Fin n ≃ Fin n) → f (tableOf (e .fst)) ≡ true
allPermutations-sound n f v e = allDistinctTables-sound (P.range n) n f v (λ i → toℕ (e .fst i))
  (λ {i} {j} p → sym (retEq e i) ∙ cong (invEq e) (toℕ-injective p) ∙ retEq e j)
  (λ i → range-member (e .fst i))
