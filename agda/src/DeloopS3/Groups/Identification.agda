{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.Identification where

-- Completeness, alternating parity, and the two normalizer subgroups.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; _+_; _<ᵇ_; isEven)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; false≢true; true≢false)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)
open import Cubical.Algebra.Group.MorphismProperties using (invGroupIso)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.FiniteReflection
open import DeloopS3.Groups.Enumerated
open import DeloopS3.Groups.Concrete
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as C
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq true true = true
boolEq _ _ = false

boolEq-sound : (x y : Bool) → boolEq x y ≡ true → x ≡ y
boolEq-sound false false p = refl
boolEq-sound true true p = refl
boolEq-sound false true p = Empty.rec (false≢true p)
boolEq-sound true false p = Empty.rec (false≢true p)

if-true : {a b : Bool} → a ≡ true → (if a then b else true) ≡ true → b ≡ true
if-true {true} p q = q
if-true {false} p q = Empty.rec (false≢true p)

inversions : P.Table → ℕ
inversions [] = 0
inversions (x ∷ xs) = P.length (P.filter (λ y → y <ᵇ x) xs) + inversions xs

evenTable : P.Table → Bool
evenTable t = isEven (inversions t)

abstract
  S₄-exhaustive : allPermutations 4 (λ t → P.member P.tableEq t (C.group O.cert)) ≡ true
  S₄-exhaustive = refl

  A₅-exhaustive : allPermutations 5 (λ t → boolEq (evenTable t) (P.member P.tableEq t (C.group I.cert))) ≡ true
  A₅-exhaustive = refl

  normalizer₄-exhaustive : allPermutations 4 (λ t → boolEq (C.normalizes O.cert t) (P.member P.tableEq t (C.subgroup O.cert))) ≡ true
  normalizer₄-exhaustive = refl

  normalizer₃-exhaustive : P.all (λ t → boolEq (C.normalizes I.cert t) (P.member P.tableEq t (C.subgroup I.cert))) (C.group I.cert) ≡ true
  normalizer₃-exhaustive = refl

  D₆-included : P.all (λ t → P.member P.tableEq t (C.group I.cert)) (C.subgroup I.cert) ≡ true
  D₆-included = refl

module D₆-inclusion = Inclusion 5 (C.subgroup I.cert) (C.group I.cert) D₆-checked A₅-checked D₆-included

D₆→A₅ : GroupHom D₆ A₅
D₆→A₅ = D₆-inclusion.hom

module Realization (n : ℕ) (ts : List P.Table) (c : CheckedTables n ts) where
  module T = FromTables n ts c

  listed : FinSymGroup n .fst → Bool
  listed e = P.member P.tableEq (certificateTable e) ts

  sound : (i : T.Carrier) → listed (T.embed i) ≡ true
  sound i = cong (λ t → P.member P.tableEq t ts) (certificateTable-roundtrip (T.table i) (T.valid i))
    ∙ member-complete P.tableEq tableEq-refl (at-member ts i)

  complete : (e : FinSymGroup n .fst) → listed e ≡ true → Σ[ i ∈ T.Carrier ] T.embed i ≡ e
  complete e m = T.locate (certificateTable e) m ,
    (T.realize (certificateTable e) m ∙ certificateTable-sound e (T.listed-valid (certificateTable e) m))

module S4R = Realization 4 (C.group O.cert) S₄-checked
module A5R = Realization 5 (C.group I.cert) A₅-checked
module D8R = Realization 4 (C.subgroup O.cert) D₈-checked

S₄-complete : (e : S₄ .fst) → S4R.listed e ≡ true
S₄-complete e = allPermutations-sound 4 (λ t → P.member P.tableEq t (C.group O.cert))
    S₄-exhaustive (invEquiv e)

S₄-tables≅S₄ : GroupIso S₄-tables.group S₄
Iso.fun (S₄-tables≅S₄ .fst) = S₄-tables.embed
Iso.inv (S₄-tables≅S₄ .fst) e = S4R.complete e (S₄-complete e) .fst
Iso.sec (S₄-tables≅S₄ .fst) e = S4R.complete e (S₄-complete e) .snd
Iso.ret (S₄-tables≅S₄ .fst) i = S₄-tables.embed-injective (S4R.complete (S₄-tables.embed i) (S₄-complete (S₄-tables.embed i)) .snd)
S₄-tables≅S₄ .snd = S₄-tables.embedding .snd

evenPermutation : FinSymGroup 5 .fst → Bool
evenPermutation e = evenTable (certificateTable e)

A₅-characterization : (e : FinSymGroup 5 .fst) → evenPermutation e ≡ A5R.listed e
A₅-characterization e = boolEq-sound _ _
  (allPermutations-sound 5 (λ t → boolEq (evenTable t) (P.member P.tableEq t (C.group I.cert)))
    A₅-exhaustive (invEquiv e))

A₅-even : (a : A₅ .fst) → evenPermutation (A₅-tables.embed a) ≡ true
A₅-even a = A₅-characterization (A₅-tables.embed a) ∙ A5R.sound a

A₅-all-even : (e : FinSymGroup 5 .fst) → evenPermutation e ≡ true
  → Σ[ a ∈ A₅ .fst ] A₅-tables.embed a ≡ e
A₅-all-even e p = A5R.complete e (sym (A₅-characterization e) ∙ p)

module Alternating = PredicateSubgroup A₅ (FinSymGroup 5) A₅→S₅ A₅-tables.embed-injective
  evenPermutation A₅-even A₅-all-even

-- Hence even permutations are a subgroup, with inherited product/inverse
-- closure, and the certified 60-element group is isomorphic to it.
A₅≅evenPermutations : GroupIso A₅ Alternating.group
A₅≅evenPermutations = Alternating.comparison

normalizes₄ : S₄ .fst → Bool
normalizes₄ e = C.normalizes O.cert (certificateTable e)

normalizer₄-characterization : (e : S₄ .fst) → normalizes₄ e ≡ D8R.listed e
normalizer₄-characterization e = boolEq-sound _ _
  (allPermutations-sound 4 (λ t → boolEq (C.normalizes O.cert t) (P.member P.tableEq t (C.subgroup O.cert)))
    normalizer₄-exhaustive (invEquiv e))

D₈-normalizes : (d : D₈ .fst) → normalizes₄ (D₈-tables.embed d) ≡ true
D₈-normalizes d = normalizer₄-characterization (D₈-tables.embed d) ∙ D8R.sound d

D₈-all-normalizers : (e : S₄ .fst) → normalizes₄ e ≡ true → Σ[ d ∈ D₈ .fst ] D₈-tables.embed d ≡ e
D₈-all-normalizers e p = D8R.complete e (sym (normalizer₄-characterization e) ∙ p)

module Normalizer₄ = PredicateSubgroup D₈ S₄ D₈→S₄ D₈-tables.embed-injective
  normalizes₄ D₈-normalizes D₈-all-normalizers

normalizes₃ : A₅ .fst → Bool
normalizes₃ a = C.normalizes I.cert (A₅-tables.table a)

normalizer₃-characterization : (a : A₅ .fst)
  → normalizes₃ a ≡ P.member P.tableEq (A₅-tables.table a) (C.subgroup I.cert)
normalizer₃-characterization a = boolEq-sound _ _
  (all-sound (λ t → boolEq (C.normalizes I.cert t) (P.member P.tableEq t (C.subgroup I.cert)))
    normalizer₃-exhaustive (at-member (C.group I.cert) a))

D₆-normalizes : (d : D₆ .fst) → normalizes₃ (D₆-inclusion.inclusion d) ≡ true
D₆-normalizes d = normalizer₃-characterization (D₆-inclusion.inclusion d)
  ∙ cong (λ t → P.member P.tableEq t (C.subgroup I.cert))
      (A₅-tables.locate-hit (D₆-tables.table d) (D₆-inclusion.membership d))
  ∙ member-complete P.tableEq tableEq-refl (at-member (C.subgroup I.cert) d)

D₆-all-normalizers : (a : A₅ .fst) → normalizes₃ a ≡ true
  → Σ[ d ∈ D₆ .fst ] D₆-inclusion.inclusion d ≡ a
D₆-all-normalizers a p = d , A₅-tables.embed-injective
  (D₆-inclusion.commutes d ∙ certificate-cong (D₆-tables.table d) (A₅-tables.table a)
    (D₆-tables.valid d) (A₅-tables.valid a) (D₆-tables.locate-hit (A₅-tables.table a) m))
  where
  m = sym (normalizer₃-characterization a) ∙ p
  d = D₆-tables.locate (A₅-tables.table a) m

module Normalizer₃ = PredicateSubgroup D₆ A₅ D₆→A₅ D₆-inclusion.injective
  normalizes₃ D₆-normalizes D₆-all-normalizers

normalizer₄≅D₈ : GroupIso Normalizer₄.group D₈
normalizer₄≅D₈ = invGroupIso Normalizer₄.comparison

normalizer₃≅D₆ : GroupIso Normalizer₃.group D₆
normalizer₃≅D₆ = invGroupIso Normalizer₃.comparison

-- Parity may equivalently be read from the literal Cubical permutation,
-- not only from its certificate-convention inverse. Inverse closure of
-- the already constructed subgroup proves that equivalence constructively.
open import Cubical.Algebra.Group.Subgroup using (isSubgroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)

literalEvenPermutation : FinSymGroup 5 .fst → Bool
literalEvenPermutation e = evenTable (tableOf (e .fst))

inverse-parity : (e : FinSymGroup 5 .fst)
  → evenPermutation (invEquiv e) ≡ literalEvenPermutation e
inverse-parity e = cong (λ e → evenTable (tableOf (e .fst)))
  (GroupTheory.invInv (FinSymGroup 5) e)

even-to-literal : (e : FinSymGroup 5 .fst) → evenPermutation e ≡ true → literalEvenPermutation e ≡ true
even-to-literal e p = sym (inverse-parity e)
  ∙ isSubgroup.inv-closed (Alternating.subgroup .snd) {x = e} p

literal-to-even : (e : FinSymGroup 5 .fst) → literalEvenPermutation e ≡ true → evenPermutation e ≡ true
literal-to-even e p = sym (cong evenPermutation (GroupTheory.invInv (FinSymGroup 5) e))
  ∙ isSubgroup.inv-closed (Alternating.subgroup .snd) {x = invEquiv e} (inverse-parity e ∙ p)

module LiteralAlternating = PredicateSubgroup A₅ (FinSymGroup 5) A₅→S₅ A₅-tables.embed-injective
  literalEvenPermutation
  (λ a → even-to-literal (A₅-tables.embed a) (A₅-even a))
  (λ e p → A₅-all-even e (literal-to-even e p))

A₅≅literalEvenPermutations : GroupIso A₅ LiteralAlternating.group
A₅≅literalEvenPermutations = LiteralAlternating.comparison
