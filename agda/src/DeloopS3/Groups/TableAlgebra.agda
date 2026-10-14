{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.TableAlgebra where

-- Generic table algebra and the certificate/SymGroup convention adapter.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; _and_)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; toℕ; toℕ-injective)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.FiniteReflection
open import DeloopS3.Groups.Enumerated
import DeloopS3.Cert.Perm as P

tableConjugate : P.Table → P.Table → P.Table
tableConjugate g x = P.compose (P.compose g x) (P.inverse g)

map-length : {A B : Type} (f : A → B) (xs : List A) → P.length (P.map f xs) ≡ P.length xs
map-length f [] = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

range-length : (n : ℕ) → P.length (P.range n) ≡ n
range-length zero = refl
range-length (suc n) = cong suc (map-length suc (P.range n) ∙ range-length n)

encode-length : {n : ℕ} (e : FinSymGroup n .fst) → P.length (certificateTable e) ≡ n
encode-length {n} e = sample-length n _

encode-value : {n : ℕ} (e : FinSymGroup n .fst) (i : Fin n)
  → P.apply (certificateTable e) (toℕ i) ≡ toℕ (invEq e i)
encode-value e = sample-nth _ _

encode-compose : {n : ℕ} (e f : FinSymGroup n .fst)
  → certificateTable (compEquiv e f) ≡ P.compose (certificateTable e) (certificateTable f)
encode-compose {n} e f = nth-ext n _ _ _ _ (encode-length (compEquiv e f))
  (map-length (P.apply (certificateTable e)) (certificateTable f) ∙ encode-length f)
  (λ i → encode-value (compEquiv e f) i
    ∙ cong (λ z → toℕ (z .fst i)) (GroupTheory.invDistr (FinSymGroup n) e f)
    ∙ sym (encode-value e (invEq f i))
    ∙ cong (P.apply (certificateTable e)) (sym (encode-value f i))
    ∙ sym (compose-apply (certificateTable e) (certificateTable f) (certificateTable-valid f) i))

search-inverse-value : {n : ℕ} (e : FinSymGroup n .fst) (i : Fin n)
  → P.findIndex (toℕ i) (certificateTable e) ≡ toℕ (e .fst i)
search-inverse-value {n} e i = sym j-value ∙ cong toℕ
  (sym (secEq e j) ∙ cong (e .fst) hit)
  where
  t = certificateTable e
  w = findIndex-witness (toℕ i) t
    (member-complete _≡ᵇ_ natEq-refl (Valid.backward {t = t} (certificateTable-valid e) _ (range-member i)))
  j = castFin (encode-length e) (w .fst)
  j-value : toℕ j ≡ P.findIndex (toℕ i) t
  j-value = castFin-value (encode-length e) (w .fst) ∙ w .snd .fst
  hit : invEq e j ≡ i
  hit = toℕ-injective (sym (encode-value e j)
    ∙ cong (P.apply t) j-value ∙ inverse-hit t (certificateTable-valid e) i)

encode-inverse : {n : ℕ} (e : FinSymGroup n .fst)
  → certificateTable (invEquiv e) ≡ P.inverse (certificateTable e)
encode-inverse {n} e = nth-ext n _ _ _ _ (encode-length (invEquiv e))
  (map-length _ (P.range (P.length (certificateTable e)))
   ∙ range-length (P.length (certificateTable e)) ∙ encode-length e)
  (λ i → encode-value (invEquiv e) i
    ∙ cong (λ z → toℕ (z .fst i)) (GroupTheory.invInv (FinSymGroup n) e)
    ∙ sym (search-inverse-value e i)
    ∙ sym (inverse-apply (certificateTable e) (certificateTable-valid e) i))

conjugate : {n : ℕ} → FinSymGroup n .fst → FinSymGroup n .fst → FinSymGroup n .fst
conjugate g x = compEquiv (compEquiv g x) (invEquiv g)

encode-conjugate : {n : ℕ} (g x : FinSymGroup n .fst)
  → certificateTable (conjugate g x) ≡ tableConjugate (certificateTable g) (certificateTable x)
encode-conjugate g x = encode-compose (compEquiv g x) (invEquiv g)
  ∙ cong₂ P.compose (encode-compose g x) (encode-inverse g)

encode-injective : {n : ℕ} (e f : FinSymGroup n .fst) → certificateTable e ≡ certificateTable f → e ≡ f
encode-injective e f p = sym (certificateTable-sound e (certificateTable-valid e))
  ∙ certificate-cong (certificateTable e) (certificateTable f) (certificateTable-valid e) (certificateTable-valid f) p
  ∙ certificateTable-sound f (certificateTable-valid f)

-- The lists normalized by the certificates are precisely powers of the
-- stated rotation: this connects the preceding finite-set semantics to
-- the cyclic-subgroup terminology.
equivPower : {n : ℕ} → FinSymGroup n .fst → ℕ → FinSymGroup n .fst
equivPower {n} r zero = idEquiv (Fin n)
equivPower r (suc k) = compEquiv (equivPower r k) r

encode-unit : (n : ℕ) → certificateTable (idEquiv (Fin n)) ≡ P.identity n
encode-unit n = nth-ext n _ 0 _ _ (encode-length (idEquiv (Fin n))) (range-length n)
  (λ i → encode-value (idEquiv (Fin n)) i ∙ sym (nth-range _ i))

encode-power : {n : ℕ} (r : FinSymGroup n .fst) (k : ℕ)
  → certificateTable (equivPower r k) ≡ P.power n (certificateTable r) k
encode-power {n} r zero = encode-unit n
encode-power r (suc k) = encode-compose (equivPower r k) r
  ∙ cong (λ t → P.compose t (certificateTable r)) (encode-power r k)


-- Total validation closure: callers need not separately re-check a
-- composed/inverted table in order to use the convention adapter.
identity-valid : (n : ℕ) → P.isPerm n (P.identity n) ≡ true
identity-valid n = subst (λ t → P.isPerm n t ≡ true) (encode-unit n)
  (certificateTable-valid (idEquiv (Fin n)))

compose-valid : {n : ℕ} (p q : P.Table)
  → P.isPerm n p ≡ true → P.isPerm n q ≡ true → P.isPerm n (P.compose p q) ≡ true
compose-valid {n} p q vp vq = subst (λ t → P.isPerm n t ≡ true)
  (encode-compose ep eq ∙ cong₂ P.compose (certificateTable-roundtrip p vp) (certificateTable-roundtrip q vq))
  (certificateTable-valid (compEquiv ep eq))
  where
  ep = certificatePermutation {n = n} {t = p} vp
  eq = certificatePermutation {n = n} {t = q} vq

inverse-valid : {n : ℕ} (p : P.Table) → P.isPerm n p ≡ true → P.isPerm n (P.inverse p) ≡ true
inverse-valid {n} p vp = subst (λ t → P.isPerm n t ≡ true)
  (encode-inverse ep ∙ cong P.inverse (certificateTable-roundtrip p vp))
  (certificateTable-valid (invEquiv ep))
  where ep = certificatePermutation {n = n} {t = p} vp

open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool using (isSetBool)
open import Cubical.Data.Nat using (discreteℕ)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Discrete→isSet)
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)

permutationPath : {n : ℕ} (p q : P.Permutation n) → P.table p ≡ P.table q → p ≡ q
permutationPath {n} p q e i = P.certified (e i)
  (isProp→PathP (λ i → isSetBool (P.isPerm n (e i)) true) (P.valid p) (P.valid q) i)

discretePermutation : {n : ℕ} → Discrete (P.Permutation n)
discretePermutation p q with discreteList discreteℕ (P.table p) (P.table q)
... | yes e = yes (permutationPath p q e)
... | no ne = no (λ e → ne (cong P.table e))

module ValidatedTables (n : ℕ) where
  unit : P.Permutation n
  unit = P.certified (P.identity n) (identity-valid n)

  mul : P.Permutation n → P.Permutation n → P.Permutation n
  mul p q = P.certified (P.compose (P.table p) (P.table q))
    (compose-valid (P.table p) (P.table q) (P.valid p) (P.valid q))

  inverse : P.Permutation n → P.Permutation n
  inverse p = P.certified (P.inverse (P.table p)) (inverse-valid (P.table p) (P.valid p))

  embed : P.Permutation n → FinSymGroup n .fst
  embed p = certificatePermutation {t = P.table p} (P.valid p)

  injective : {p q : P.Permutation n} → embed p ≡ embed q → p ≡ q
  injective {p} {q} e = permutationPath p q
    (certificatePermutation-injective (P.table p) (P.table q) (P.valid p) (P.valid q) e)

  private
    module Inherit = Induced (Discrete→isSet discretePermutation) (FinSymGroup n) embed injective
      unit mul inverse (certificatePermutation-identity n (identity-valid n))
      (λ p q → certificatePermutation-compose (P.table p) (P.table q) (P.valid p) (P.valid q) (P.valid (mul p q)))
      (λ p → certificatePermutation-inverse (P.table p) (P.valid p) (P.valid (inverse p)))

  group : Group₀
  group = Inherit.induced

  adapter : GroupHom group (FinSymGroup n)
  adapter = Inherit.embedding

  comparison : GroupIso group (FinSymGroup n)
  Iso.fun (comparison .fst) = embed
  Iso.inv (comparison .fst) e = P.certified (certificateTable e) (certificateTable-valid e)
  Iso.sec (comparison .fst) e = certificateTable-sound e (certificateTable-valid e)
  Iso.ret (comparison .fst) p = permutationPath _ p (certificateTable-roundtrip (P.table p) (P.valid p))
  comparison .snd = adapter .snd

TableGroup : ℕ → Group₀
TableGroup = ValidatedTables.group

certificateAdapter : (n : ℕ) → GroupHom (TableGroup n) (FinSymGroup n)
certificateAdapter = ValidatedTables.adapter

TableGroup≅SymGroup : (n : ℕ) → GroupIso (TableGroup n) (FinSymGroup n)
TableGroup≅SymGroup = ValidatedTables.comparison
