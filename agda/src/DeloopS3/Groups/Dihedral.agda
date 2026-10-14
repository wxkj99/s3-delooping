{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.Dihedral where

-- Explicit (i,ε)(j,δ)=(i+(-1)^ε j,ε xor δ) pair groups.
-- Only e=3,4 are required: finite reflected homomorphism checks inherit
-- the group laws and prove bijectivity onto the certified normalizers.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; false; _and_; _or_; not; _⊕_; if_then_else_; isSetBool; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; toℕ; toℕ-injective; isSetFin; SumFin→Fin; Fin→SumFin)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.FiniteReflection
open import DeloopS3.Groups.Enumerated
open import DeloopS3.Groups.Concrete
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as C
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I

sameBool : Bool → Bool → Bool
sameBool false false = true
sameBool true true = true
sameBool _ _ = false

sameBool-sound : (x y : Bool) → sameBool x y ≡ true → x ≡ y
sameBool-sound false false p = refl
sameBool-sound true true p = refl
sameBool-sound false true p = Empty.rec (false≢true p)
sameBool-sound true false p = Empty.rec (false≢true p)

implication : {a b : Bool} → not a or b ≡ true → a ≡ true → b ≡ true
implication {true} p q = p
implication {false} p q = Empty.rec (false≢true q)

module Pairs (e : ℕ) where
  Pair = Fin (suc e) × Bool

  add : Fin (suc e) → Fin (suc e) → Fin (suc e)
  add i j = Fin→SumFin (GroupStr._·_ ((ℤGroup/ (suc e)) .snd) (SumFin→Fin i) (SumFin→Fin j))

  neg : Fin (suc e) → Fin (suc e)
  neg i = Fin→SumFin (GroupStr.inv ((ℤGroup/ (suc e)) .snd) (SumFin→Fin i))

  unit : Pair
  unit = fzero , false

  mul : Pair → Pair → Pair
  mul (i , b) (j , c) = add i (if b then neg j else j) , (b ⊕ c)

  inverse : Pair → Pair
  inverse (i , b) = (if b then i else neg i) , b

  eq : Pair → Pair → Bool
  eq (i , b) (j , c) = (toℕ i ≡ᵇ toℕ j) and sameBool b c

  eq-sound : (x y : Pair) → eq x y ≡ true → x ≡ y
  eq-sound (i , b) (j , c) p = cong₂ _,_
    (toℕ-injective (natEq-sound _ _ (and-left p))) (sameBool-sound b c (and-right p))

  allPairs : (Pair → Bool) → Bool
  allPairs f = allFin (λ i → f (i , false) and f (i , true))

  allPairs-sound : (f : Pair → Bool) → allPairs f ≡ true → (p : Pair) → f p ≡ true
  allPairs-sound f v (i , false) = and-left (allFin-sound (λ i → f (i , false) and f (i , true)) v i)
  allPairs-sound f v (i , true) = and-right (allFin-sound (λ i → f (i , false) and f (i , true)) v i)

  pairs : List Pair
  pairs = P.concatMap (λ i → (i , false) ∷ (i , true) ∷ []) (sample (suc e) (λ i → i))

module PairTables (n e : ℕ) (r s : P.Table) where
  open Pairs e public

  table : Pair → P.Table
  table (i , b) = P.compose (P.power n r (toℕ i)) (if b then s else P.identity n)

  record Checked : Type where
    field
      valid : allPairs (P.isPerm n ∘ table) ≡ true
      faithful : allPairs (λ x → allPairs (λ y → not (P.tableEq (table x) (table y)) or eq x y)) ≡ true
      unit-ok : P.tableEq (table unit) (P.identity n) ≡ true
      product-ok : allPairs (λ x → allPairs (λ y → P.tableEq (table (mul x y)) (P.compose (table x) (table y)))) ≡ true
      inverse-ok : allPairs (λ x → P.tableEq (table (inverse x)) (P.inverse (table x))) ≡ true

  module Build (checked : Checked) where
    open Checked checked

    validAt : (x : Pair) → P.isPerm n (table x) ≡ true
    validAt = allPairs-sound (P.isPerm n ∘ table) valid

    embed : Pair → FinSymGroup n .fst
    embed x = certificatePermutation {t = table x} (validAt x)

    injective : {x y : Pair} → embed x ≡ embed y → x ≡ y
    injective {x} {y} p = eq-sound x y (implication
      (allPairs-sound (λ y → not (P.tableEq (table x) (table y)) or eq x y)
        (allPairs-sound (λ x → allPairs (λ y → not (P.tableEq (table x) (table y)) or eq x y)) faithful x) y)
      (cong (P.tableEq (table x)) (sym t) ∙ tableEq-refl (table x)))
      where t = certificatePermutation-injective (table x) (table y) (validAt x) (validAt y) p

    unit-path = tableEq-sound (table unit) (P.identity n) unit-ok
    unit-valid = subst (λ t → P.isPerm n t ≡ true) unit-path (validAt unit)

    embed-unit : embed unit ≡ idEquiv (Fin n)
    embed-unit = certificate-cong (table unit) (P.identity n) (validAt unit) unit-valid unit-path
      ∙ certificatePermutation-identity n unit-valid

    product-path : (x y : Pair) → table (mul x y) ≡ P.compose (table x) (table y)
    product-path x y = tableEq-sound _ _ (allPairs-sound (λ y → P.tableEq (table (mul x y)) (P.compose (table x) (table y)))
      (allPairs-sound (λ x → allPairs (λ y → P.tableEq (table (mul x y)) (P.compose (table x) (table y)))) product-ok x) y)

    embed-product : (x y : Pair) → embed (mul x y) ≡ compEquiv (embed x) (embed y)
    embed-product x y = certificate-cong (table (mul x y)) (P.compose (table x) (table y))
      (validAt (mul x y)) v (product-path x y)
      ∙ certificatePermutation-compose (table x) (table y) (validAt x) (validAt y) v
      where v = subst (λ t → P.isPerm n t ≡ true) (product-path x y) (validAt (mul x y))

    inverse-path : (x : Pair) → table (inverse x) ≡ P.inverse (table x)
    inverse-path x = tableEq-sound _ _ (allPairs-sound (λ x → P.tableEq (table (inverse x)) (P.inverse (table x))) inverse-ok x)

    embed-inverse : (x : Pair) → embed (inverse x) ≡ invEquiv (embed x)
    embed-inverse x = certificate-cong (table (inverse x)) (P.inverse (table x)) (validAt (inverse x)) v (inverse-path x)
      ∙ certificatePermutation-inverse (table x) (validAt x) v
      where v = subst (λ t → P.isPerm n t ≡ true) (inverse-path x) (validAt (inverse x))

    module Inherit = Induced (isSet× isSetFin isSetBool) (FinSymGroup n) embed injective
      unit mul inverse embed-unit embed-product embed-inverse

    group : Group₀
    group = Inherit.induced

    module Compare (ts : List P.Table) (ct : CheckedTables n ts)
      (into : allPairs (λ x → P.member P.tableEq (table x) ts) ≡ true)
      (onto : P.all (λ t → P.member P.tableEq t (P.map table pairs)) ts ≡ true) where
      module T = FromTables n ts ct

      memberAt = allPairs-sound (λ x → P.member P.tableEq (table x) ts) into
      forward : Pair → T.Carrier
      forward x = T.locate (table x) (memberAt x)
      commutes : (x : Pair) → T.embed (forward x) ≡ embed x
      commutes x = certificate-cong (T.table (forward x)) (table x) (T.valid (forward x)) (validAt x)
        (T.locate-hit (table x) (memberAt x))

      preimage : (i : T.Carrier) → Σ[ x ∈ Pair ] forward x ≡ i
      preimage i = w .fst , T.embed-injective
        (commutes (w .fst) ∙ certificate-cong (table (w .fst)) (T.table i) (validAt (w .fst)) (T.valid i) (w .snd .snd))
        where
        w = map-member⁻ table pairs (member-sound P.tableEq tableEq-sound (T.table i) (P.map table pairs)
          (all-sound (λ t → P.member P.tableEq t (P.map table pairs)) onto (at-member ts i)))

      comparison : GroupIso group T.group
      Iso.fun (comparison .fst) = forward
      Iso.inv (comparison .fst) i = preimage i .fst
      Iso.sec (comparison .fst) i = preimage i .snd
      Iso.ret (comparison .fst) x = injective
        (sym (commutes (preimage (forward x) .fst))
         ∙ cong T.embed (preimage (forward x) .snd) ∙ commutes x)
      comparison .snd = makeIsGroupHom λ x y → T.embed-injective
        (commutes (mul x y) ∙ embed-product x y
         ∙ sym (T.embed-mul (forward x) (forward y) ∙ cong₂ compEquiv (commutes x) (commutes y)))

-- Rotations/reflections in certificate (p ∘ q) convention.
r₄ s₄ r₃ s₃ : P.Table
r₄ = 3 ∷ 0 ∷ 1 ∷ 2 ∷ []       -- (1432)
s₄ = 2 ∷ 1 ∷ 0 ∷ 3 ∷ []       -- (13)
r₃ = 0 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []   -- (235)
s₃ = 3 ∷ 1 ∷ 4 ∷ 0 ∷ 2 ∷ []   -- (14)(35)

module P₈ = PairTables 4 3 r₄ s₄
module P₆ = PairTables 5 2 r₃ s₃

abstract
  checked₈ : P₈.Checked
  P₈.Checked.valid checked₈ = refl
  P₈.Checked.faithful checked₈ = refl
  P₈.Checked.unit-ok checked₈ = refl
  P₈.Checked.product-ok checked₈ = refl
  P₈.Checked.inverse-ok checked₈ = refl

  checked₆ : P₆.Checked
  P₆.Checked.valid checked₆ = refl
  P₆.Checked.faithful checked₆ = refl
  P₆.Checked.unit-ok checked₆ = refl
  P₆.Checked.product-ok checked₆ = refl
  P₆.Checked.inverse-ok checked₆ = refl

  into₈ : P₈.allPairs (λ x → P.member P.tableEq (P₈.table x) (C.subgroup O.cert)) ≡ true
  into₈ = refl
  onto₈ : P.all (λ t → P.member P.tableEq t (P.map P₈.table P₈.pairs)) (C.subgroup O.cert) ≡ true
  onto₈ = refl
  into₆ : P₆.allPairs (λ x → P.member P.tableEq (P₆.table x) (C.subgroup I.cert)) ≡ true
  into₆ = refl
  onto₆ : P.all (λ t → P.member P.tableEq t (P.map P₆.table P₆.pairs)) (C.subgroup I.cert) ≡ true
  onto₆ = refl

module Dihedral₈ = P₈.Build checked₈
module Dihedral₆ = P₆.Build checked₆
module Compare₈ = Dihedral₈.Compare (C.subgroup O.cert) D₈-checked into₈ onto₈
module Compare₆ = Dihedral₆.Compare (C.subgroup I.cert) D₆-checked into₆ onto₆

D₈-pairs≅D₈ : GroupIso Dihedral₈.group D₈
D₈-pairs≅D₈ = Compare₈.comparison

D₆-pairs≅D₆ : GroupIso Dihedral₆.group D₆
D₆-pairs≅D₆ = Compare₆.comparison
