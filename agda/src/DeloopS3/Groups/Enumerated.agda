{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.Enumerated where

-- Finite enumerations become genuine groups, by reflection of
-- closure and inheritance of laws from FinSymGroup, not by their length.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; _and_)
open import Cubical.Data.List.Base using (List)
open import Cubical.Data.SumFin using (Fin; isSetFin; discreteFin; toℕ; toℕ-injective)
open import Cubical.Relation.Nullary using (Discrete)
open import Cubical.Algebra.Group.Base hiding (group)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import DeloopS3.Groups.TablePermutation
import DeloopS3.Cert.Perm as P

record ConcreteGroup (N : ℕ) : Type₁ where
  field
    group : Group₀
    enumerate : group .fst ≃ Fin N
    decEq : Discrete (group .fst)

module Induced {A : Type} (setA : isSet A) (G : Group₀)
  (f : A → G .fst) (inj : {x y : A} → f x ≡ f y → x ≡ y)
  (e : A) (mul : A → A → A) (inverse : A → A)
  (fe : f e ≡ GroupStr.1g (G .snd))
  (fm : (x y : A) → f (mul x y) ≡ GroupStr._·_ (G .snd) (f x) (f y))
  (fi : (x : A) → f (inverse x) ≡ GroupStr.inv (G .snd) (f x)) where
  private module G = GroupStr (G .snd)

  induced : Group₀
  induced = makeGroup e mul inverse setA
    (λ x y z → inj (fm x (mul y z) ∙ cong (f x G.·_) (fm y z)
       ∙ G.·Assoc (f x) (f y) (f z)
       ∙ sym (fm (mul x y) z ∙ cong (G._· f z) (fm x y))))
    (λ x → inj (fm x e ∙ cong (f x G.·_) fe ∙ G.·IdR (f x)))
    (λ x → inj (fm e x ∙ cong (G._· f x) fe ∙ G.·IdL (f x)))
    (λ x → inj (fm x (inverse x) ∙ cong (f x G.·_) (fi x)
       ∙ G.·InvR (f x) ∙ sym fe))
    (λ x → inj (fm (inverse x) x ∙ cong (G._· f x) (fi x)
       ∙ G.·InvL (f x) ∙ sym fe))

  embedding : GroupHom induced G
  embedding = f , makeIsGroupHom fm

record CheckedTables (n : ℕ) (ts : List P.Table) : Type where
  field
    permutations : P.all (P.isPerm n) ts ≡ true
    distinct : P.unique P.tableEq ts ≡ true
    unit-closed : P.member P.tableEq (P.identity n) ts ≡ true
    product-closed : P.all (λ p → P.all (λ q → P.member P.tableEq (P.compose p q) ts) ts) ts ≡ true
    inverse-closed : P.all (λ p → P.member P.tableEq (P.inverse p) ts) ts ≡ true

-- This transport lemma deliberately ignores validation-proof choices.
-- All interpretations have the same literal table as their function.
table-cong : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true) → p ≡ q
  → tablePermutation {t = p} vp ≡ tablePermutation {t = q} vq
table-cong p q vp vq e = equivEq (funExt λ i → Cubical.Data.SumFin.toℕ-injective
  (tablePermutation-value {t = p} vp i
   ∙ cong (λ t → P.apply t (Cubical.Data.SumFin.toℕ i)) e
   ∙ sym (tablePermutation-value {t = q} vq i)))

certificate-cong : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true) → p ≡ q
  → certificatePermutation {t = p} vp ≡ certificatePermutation {t = q} vq
certificate-cong p q vp vq e = cong invEquiv (table-cong p q vp vq e)

module FromTables (n : ℕ) (ts : List P.Table) (checked : CheckedTables n ts) where
  open CheckedTables checked
  Carrier = Fin (P.length ts)

  table : Carrier → P.Table
  table = at ts

  valid : (i : Carrier) → P.isPerm n (table i) ≡ true
  valid i = all-sound (P.isPerm n) permutations (at-member ts i)

  embed : Carrier → FinSymGroup n .fst
  embed i = certificatePermutation {t = table i} (valid i)

  embed-injective : {i j : Carrier} → embed i ≡ embed j → i ≡ j
  embed-injective {i} {j} p = unique-injective P.tableEq tableEq-refl ts distinct i j
    (certificatePermutation-injective (table i) (table j) (valid i) (valid j) p)

  locate : (t : P.Table) → P.member P.tableEq t ts ≡ true → Carrier
  locate t m = member-index (member-sound P.tableEq tableEq-sound t ts m) .fst

  locate-hit : (t : P.Table) (m : P.member P.tableEq t ts ≡ true) → table (locate t m) ≡ t
  locate-hit t m = member-index (member-sound P.tableEq tableEq-sound t ts m) .snd

  listed-valid : (t : P.Table) (m : P.member P.tableEq t ts ≡ true) → P.isPerm n t ≡ true
  listed-valid t m = subst (λ t → P.isPerm n t ≡ true) (locate-hit t m) (valid (locate t m))

  realize : (t : P.Table) (m : P.member P.tableEq t ts ≡ true)
    → embed (locate t m) ≡ certificatePermutation {t = t} (listed-valid t m)
  realize t m = certificate-cong (table (locate t m)) t (valid (locate t m))
    (listed-valid t m) (locate-hit t m)

  unit : Carrier
  unit = locate (P.identity n) unit-closed

  closed-product : (i j : Carrier) → P.member P.tableEq (P.compose (table i) (table j)) ts ≡ true
  closed-product i j = all-sound (λ q → P.member P.tableEq (P.compose (table i) q) ts)
    (all-sound (λ p → P.all (λ q → P.member P.tableEq (P.compose p q) ts) ts)
      product-closed (at-member ts i)) (at-member ts j)

  mul : Carrier → Carrier → Carrier
  mul i j = locate (P.compose (table i) (table j)) (closed-product i j)

  closed-inverse : (i : Carrier) → P.member P.tableEq (P.inverse (table i)) ts ≡ true
  closed-inverse i = all-sound (λ p → P.member P.tableEq (P.inverse p) ts)
    inverse-closed (at-member ts i)

  inverse : Carrier → Carrier
  inverse i = locate (P.inverse (table i)) (closed-inverse i)

  embed-unit : embed unit ≡ idEquiv (Fin n)
  embed-unit = realize (P.identity n) unit-closed
    ∙ certificatePermutation-identity n (listed-valid (P.identity n) unit-closed)

  embed-mul : (i j : Carrier) → embed (mul i j) ≡ compEquiv (embed i) (embed j)
  embed-mul i j = realize (P.compose (table i) (table j)) (closed-product i j)
    ∙ certificatePermutation-compose (table i) (table j) (valid i) (valid j)
        (listed-valid (P.compose (table i) (table j)) (closed-product i j))

  embed-inverse : (i : Carrier) → embed (inverse i) ≡ invEquiv (embed i)
  embed-inverse i = realize (P.inverse (table i)) (closed-inverse i)
    ∙ certificatePermutation-inverse (table i) (valid i)
        (listed-valid (P.inverse (table i)) (closed-inverse i))

  private
    module Inherit = Induced isSetFin (FinSymGroup n) embed embed-injective
      unit mul inverse embed-unit embed-mul embed-inverse

  group : Group₀
  group = Inherit.induced

  embedding : GroupHom group (FinSymGroup n)
  embedding = Inherit.embedding

  concrete : ConcreteGroup (P.length ts)
  ConcreteGroup.group concrete = group
  ConcreteGroup.enumerate concrete = idEquiv Carrier
  ConcreteGroup.decEq concrete = discreteFin

module Inclusion (n : ℕ) (small big : List P.Table)
  (cs : CheckedTables n small) (cb : CheckedTables n big)
  (included : P.all (λ t → P.member P.tableEq t big) small ≡ true) where
  module S = FromTables n small cs
  module B = FromTables n big cb

  membership : (i : S.Carrier) → P.member P.tableEq (S.table i) big ≡ true
  membership i = all-sound (λ t → P.member P.tableEq t big) included (at-member small i)

  inclusion : S.Carrier → B.Carrier
  inclusion i = B.locate (S.table i) (membership i)

  commutes : (i : S.Carrier) → B.embed (inclusion i) ≡ S.embed i
  commutes i = certificate-cong (B.table (inclusion i)) (S.table i)
    (B.valid (inclusion i)) (S.valid i) (B.locate-hit (S.table i) (membership i))

  injective : {i j : S.Carrier} → inclusion i ≡ inclusion j → i ≡ j
  injective {i} {j} p = S.embed-injective (sym (commutes i) ∙ cong B.embed p ∙ commutes j)

  hom : GroupHom S.group B.group
  hom = inclusion , makeIsGroupHom λ i j → B.embed-injective
    (commutes (S.mul i j) ∙ S.embed-mul i j
     ∙ sym (B.embed-mul (inclusion i) (inclusion j) ∙ cong₂ compEquiv (commutes i) (commutes j)))

open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool using (isSetBool)
open import Cubical.Algebra.Group.Subgroup using (Subgroup; isSubgroup; Subgroup→Group)

-- A reflected predicate with a complete, injective group enumeration
-- inherits the actual ambient operations and is a subgroup, not just a set.
module PredicateSubgroup (A G : Group₀) (f : GroupHom A G)
  (inj : {x y : A .fst} → f .fst x ≡ f .fst y → x ≡ y)
  (test : G .fst → Bool)
  (sound : (x : A .fst) → test (f .fst x) ≡ true)
  (complete : (y : G .fst) → test y ≡ true → Σ[ x ∈ A .fst ] f .fst x ≡ y) where
  private
    module A = GroupStr (A .snd)
    module G = GroupStr (G .snd)
    module F = IsGroupHom (f .snd)

  predicate : G .fst → Type
  predicate y = test y ≡ true

  prop : (y : G .fst) → isProp (predicate y)
  prop y = isSetBool _ _

  subgroup : Subgroup G
  subgroup .fst y = predicate y , prop y
  isSubgroup.id-closed (subgroup .snd) = subst predicate F.pres1 (sound A.1g)
  isSubgroup.op-closed (subgroup .snd) {x} {y} px py =
    let a = complete x px
        b = complete y py
    in subst predicate (F.pres· (a .fst) (b .fst) ∙ cong₂ G._·_ (a .snd) (b .snd))
         (sound (a .fst A.· b .fst))
  isSubgroup.inv-closed (subgroup .snd) {x} px =
    let a = complete x px
    in subst predicate (F.presinv (a .fst) ∙ cong G.inv (a .snd)) (sound (A.inv (a .fst)))

  group : Group₀
  group = Subgroup→Group G subgroup

  comparison : GroupIso A group
  Iso.fun (comparison .fst) x = f .fst x , sound x
  Iso.inv (comparison .fst) (y , py) = complete y py .fst
  Iso.sec (comparison .fst) (y , py) = Σ≡Prop prop (complete y py .snd)
  Iso.ret (comparison .fst) x = inj (complete (f .fst x) (sound x) .snd)
  comparison .snd = makeIsGroupHom λ x y → Σ≡Prop prop (F.pres· x y)
