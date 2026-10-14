{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.TablePermutation where

-- Proof-producing interpretation of Cert.Perm tables.
-- Fin is Cubical.Data.SumFin.Fin, exactly the carrier used by FinSymGroup.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; false; _and_; _or_; not; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ; toℕ-injective)
open import Cubical.Data.Empty as Empty using (⊥)
import DeloopS3.Cert.Perm as P

private variable A B : Type

and-left : {a b : Bool} → a and b ≡ true → a ≡ true
and-left {true} p = refl
and-left {false} p = Empty.rec (false≢true p)

and-right : {a b : Bool} → a and b ≡ true → b ≡ true
and-right {true} p = p
and-right {false} p = Empty.rec (false≢true p)

natEq-sound : (x y : ℕ) → (x ≡ᵇ y) ≡ true → x ≡ y
natEq-sound zero zero p = refl
natEq-sound zero (suc y) p = Empty.rec (false≢true p)
natEq-sound (suc x) zero p = Empty.rec (false≢true p)
natEq-sound (suc x) (suc y) p = cong suc (natEq-sound x y p)

natEq-refl : (x : ℕ) → (x ≡ᵇ x) ≡ true
natEq-refl zero = refl
natEq-refl (suc x) = natEq-refl x

infix 4 _∈_
data _∈_ {A : Type} (x : A) : List A → Type where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

all-sound : (f : A → Bool) {xs : List A} → P.all f xs ≡ true
  → {x : A} → x ∈ xs → f x ≡ true
all-sound f {xs = _ ∷ _} p here = and-left p
all-sound f {xs = _ ∷ _} p (there m) = all-sound f (and-right p) m

member-sound : (eq : A → A → Bool)
  → ((x y : A) → eq x y ≡ true → x ≡ y)
  → (x : A) (xs : List A) → P.member eq x xs ≡ true → x ∈ xs
member-sound eq sound x [] p = Empty.rec (false≢true p)
member-sound eq sound x (y ∷ ys) p with eq x y | sound x y
... | true | s = subst (λ z → z ∈ (y ∷ ys)) (sym (s refl)) here
... | false | s = there (member-sound eq sound x ys p)

member-complete : (eq : A → A → Bool) → ((x : A) → eq x x ≡ true)
  → {x : A} {xs : List A} → x ∈ xs → P.member eq x xs ≡ true
member-complete eq r {x} {xs = x ∷ xs} here = cong (_or P.member eq x xs) (r x)
member-complete eq r {x} {xs = y ∷ ys} (there m) with eq x y
... | true = refl
... | false = member-complete eq r m

at : (xs : List A) → Fin (P.length xs) → A
at (x ∷ xs) fzero = x
at (x ∷ xs) (fsuc i) = at xs i

at-member : (xs : List A) (i : Fin (P.length xs)) → at xs i ∈ xs
at-member (x ∷ xs) fzero = here
at-member (x ∷ xs) (fsuc i) = there (at-member xs i)

member-index : {x : A} {xs : List A} → x ∈ xs
  → Σ[ i ∈ Fin (P.length xs) ] at xs i ≡ x
member-index here = fzero , refl
member-index (there m) = fsuc (member-index m .fst) , member-index m .snd

map-member⁻ : (f : A → B) {y : B} (xs : List A) → y ∈ P.map f xs
  → Σ[ x ∈ A ] (x ∈ xs) × (f x ≡ y)
map-member⁻ f (x ∷ xs) here = x , here , refl
map-member⁻ f (x ∷ xs) (there m) =
  let z = map-member⁻ f xs m in z .fst , there (z .snd .fst) , z .snd .snd

range-bound : (n x : ℕ) → x ∈ P.range n → Σ[ i ∈ Fin n ] toℕ i ≡ x
range-bound (suc n) zero here = fzero , refl
range-bound (suc n) x (there m) =
  let z = map-member⁻ suc (P.range n) m
      b = range-bound n (z .fst) (z .snd .fst)
  in fsuc (b .fst) , cong suc (b .snd) ∙ z .snd .snd

map-member : (f : A → B) {x : A} {xs : List A} → x ∈ xs → f x ∈ P.map f xs
map-member f here = here
map-member f (there m) = there (map-member f m)

range-member : {n : ℕ} (i : Fin n) → toℕ i ∈ P.range n
range-member {suc n} fzero = here
range-member {suc n} (fsuc i) = there (map-member suc (range-member i))

unique-injective : (eq : A → A → Bool) → ((x : A) → eq x x ≡ true)
  → (xs : List A) → P.unique eq xs ≡ true
  → (i j : Fin (P.length xs)) → at xs i ≡ at xs j → i ≡ j
unique-injective eq r (x ∷ xs) u fzero fzero p = refl
unique-injective eq r (x ∷ xs) u fzero (fsuc j) p = Empty.rec
  (false≢true (sym (cong not m) ∙ and-left u))
  where
  m : P.member eq x xs ≡ true
  m = member-complete eq r (subst (_∈ xs) (sym p) (at-member xs j))
unique-injective eq r (x ∷ xs) u (fsuc i) fzero p =
  sym (unique-injective eq r (x ∷ xs) u fzero (fsuc i) (sym p))
unique-injective eq r (x ∷ xs) u (fsuc i) (fsuc j) p =
  cong fsuc (unique-injective eq r xs (and-right u) i j p)

-- Cast an index along a proved length, retaining its numerical value.
castFin : {m n : ℕ} → m ≡ n → Fin m → Fin n
castFin p = subst Fin p

castFin-value : {m n : ℕ} (p : m ≡ n) (i : Fin m) → toℕ (castFin p i) ≡ toℕ i
castFin-value {m} p i = J (λ n p → toℕ (castFin p i) ≡ toℕ i)
  (cong toℕ (substRefl {B = Fin} i)) p

module Valid {n : ℕ} {t : P.Table} (v : P.isPerm n t ≡ true) where
  len : P.length t ≡ n
  len = natEq-sound _ _ (and-left v)

  rest : P.unique _≡ᵇ_ t and P.setEq _≡ᵇ_ t (P.range n) ≡ true
  rest = and-right {a = P.length t ≡ᵇ n} v

  sets : P.setEq _≡ᵇ_ t (P.range n) ≡ true
  sets = and-right {a = P.unique _≡ᵇ_ t} rest

  uniq : P.unique _≡ᵇ_ t ≡ true
  uniq = and-left rest

  forward : (x : ℕ) → x ∈ t → x ∈ P.range n
  forward x m = member-sound _≡ᵇ_ natEq-sound x (P.range n)
    (all-sound (λ x → P.member _≡ᵇ_ x (P.range n)) (and-left sets) m)

  backward : (x : ℕ) → x ∈ P.range n → x ∈ t
  backward x m = member-sound _≡ᵇ_ natEq-sound x t
    (all-sound (λ x → P.member _≡ᵇ_ x t)
      (and-right {a = P.all (λ x → P.member _≡ᵇ_ x (P.range n)) t} sets) m)

  index : Fin n → Fin (P.length t)
  index = castFin (sym len)

  value : Fin n → ℕ
  value i = at t (index i)

  fun : Fin n → Fin n
  fun i = range-bound n (value i) (forward _ (at-member t (index i))) .fst

  fun-value : (i : Fin n) → toℕ (fun i) ≡ value i
  fun-value i = range-bound n (value i) (forward _ (at-member t (index i))) .snd

  injective : {i j : Fin n} → fun i ≡ fun j → i ≡ j
  injective {i} {j} p = toℕ-injective
    (sym (castFin-value (sym len) i)
    ∙ cong toℕ (unique-injective _≡ᵇ_ natEq-refl t uniq (index i) (index j)
       (sym (fun-value i) ∙ cong toℕ p ∙ fun-value j))
    ∙ castFin-value (sym len) j)

  preimage : (j : Fin n) → Σ[ i ∈ Fin n ] fun i ≡ j
  preimage j = castFin len k , toℕ-injective
    (fun-value (castFin len k) ∙ cong (at t) index-path ∙ hit)
    where
    witness = member-index (backward (toℕ j) (range-member j))
    k = witness .fst
    hit = witness .snd
    index-path : index (castFin len k) ≡ k
    index-path = toℕ-injective
      (castFin-value (sym len) (castFin len k) ∙ castFin-value len k)

  tableIso : Iso (Fin n) (Fin n)
  Iso.fun tableIso = fun
  Iso.inv tableIso j = preimage j .fst
  Iso.sec tableIso j = preimage j .snd
  Iso.ret tableIso i = injective (preimage (fun i) .snd)

at-nth : (d : A) (xs : List A) (i : Fin (P.length xs))
  → P.nth d xs (toℕ i) ≡ at xs i
at-nth d (x ∷ xs) fzero = refl
at-nth d (x ∷ xs) (fsuc i) = at-nth d xs i

nth-map : (d : B) (f : A → B) (xs : List A) (i : Fin (P.length xs))
  → P.nth d (P.map f xs) (toℕ i) ≡ f (at xs i)
nth-map d f (x ∷ xs) fzero = refl
nth-map d f (x ∷ xs) (fsuc i) = nth-map d f xs i

-- Keep equivalence proof terms opaque at concrete degrees.
abstract
  tablePermutation : {n : ℕ} {t : P.Table} → P.isPerm n t ≡ true → Fin n ≃ Fin n
  tablePermutation {t = t} v = isoToEquiv (Valid.tableIso {t = t} v)

  tablePermutation-value : {n : ℕ} {t : P.Table} (v : P.isPerm n t ≡ true) (i : Fin n)
    → toℕ (tablePermutation {t = t} v .fst i) ≡ P.apply t (toℕ i)
  tablePermutation-value {t = t} v i = Valid.fun-value {t = t} v i
    ∙ sym (at-nth (P.length t) t (Valid.index {t = t} v i))
    ∙ cong (P.apply t) (castFin-value (sym (Valid.len {t = t} v)) i)


-- The literal table is an anti-homomorphism into SymGroup. Inverting
-- its equivalence is the uniform convention adapter.
certificatePermutation : {n : ℕ} {t : P.Table} → P.isPerm n t ≡ true → Fin n ≃ Fin n
certificatePermutation {t = t} v = invEquiv (tablePermutation {t = t} v)

compose-apply : {n : ℕ} (p q : P.Table) (vq : P.isPerm n q ≡ true) (i : Fin n)
  → P.apply (P.compose p q) (toℕ i) ≡ P.apply p (P.apply q (toℕ i))
compose-apply p q vq i =
  cong (P.apply (P.compose p q)) (sym (castFin-value (sym (Valid.len {t = q} vq)) i))
  ∙ nth-map (P.length (P.compose p q)) (P.apply p) q (Valid.index {t = q} vq i)
  ∙ cong (P.apply p)
      (sym (at-nth (P.length q) q (Valid.index {t = q} vq i))
       ∙ cong (P.apply q) (castFin-value (sym (Valid.len {t = q} vq)) i))

-- Composition is reverse compEquiv, NOT compEquiv in certificate order.
-- The result validation is explicit so existing certificate refl checks
-- may supply it without normalizing a generic validation theorem.
tablePermutation-compose : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
  (vpq : P.isPerm n (P.compose p q) ≡ true)
  → tablePermutation {t = P.compose p q} vpq
    ≡ compEquiv (tablePermutation {t = q} vq) (tablePermutation {t = p} vp)
tablePermutation-compose p q vp vq vpq = equivEq (funExt λ i → toℕ-injective
  (tablePermutation-value {t = P.compose p q} vpq i ∙ compose-apply p q vq i
   ∙ sym (tablePermutation-value {t = p} vp (tablePermutation {t = q} vq .fst i)
     ∙ cong (P.apply p) (tablePermutation-value {t = q} vq i))))

natEq-sym : (x y : ℕ) → (x ≡ᵇ y) ≡ (y ≡ᵇ x)
natEq-sym zero zero = refl
natEq-sym zero (suc y) = refl
natEq-sym (suc x) zero = refl
natEq-sym (suc x) (suc y) = natEq-sym x y

-- Searching a listed value produces a bounded index and its exact value.
findIndex-witness : (y : ℕ) (xs : P.Table) → P.member _≡ᵇ_ y xs ≡ true
  → Σ[ i ∈ Fin (P.length xs) ] (toℕ i ≡ P.findIndex y xs) × (at xs i ≡ y)
findIndex-witness y [] p = Empty.rec (false≢true p)
findIndex-witness y (x ∷ xs) p with x ≡ᵇ y | natEq-sound x y | natEq-sym x y
... | true | s | e = fzero , refl , s refl
... | false | s | e = fsuc (w .fst) , cong suc (w .snd .fst) , w .snd .snd
  where
  w = findIndex-witness y xs (cong (_or P.member _≡ᵇ_ y xs) e ∙ p)

nth-map-range : {n : ℕ} (d : A) (f : ℕ → A) (i : Fin n)
  → P.nth d (P.map f (P.range n)) (toℕ i) ≡ f (toℕ i)
nth-map-range {n = suc n} d f fzero = refl
nth-map-range {n = suc n} d f (fsuc i) =
  cong (λ xs → P.nth d xs (toℕ i)) (map-map f suc (P.range n))
  ∙ nth-map-range d (λ x → f (suc x)) i
  where
  map-map : (f : ℕ → A) (g : ℕ → ℕ) (xs : List ℕ)
    → P.map f (P.map g xs) ≡ P.map (λ x → f (g x)) xs
  map-map f g [] = refl
  map-map f g (x ∷ xs) = cong (f (g x) ∷_) (map-map f g xs)

inverse-apply : {n : ℕ} (p : P.Table) (vp : P.isPerm n p ≡ true) (j : Fin n)
  → P.apply (P.inverse p) (toℕ j) ≡ P.findIndex (toℕ j) p
inverse-apply p vp j =
  cong (P.apply (P.inverse p)) (sym (castFin-value (sym (Valid.len {t = p} vp)) j))
  ∙ nth-map-range {n = P.length p} (P.length (P.inverse p)) (λ y → P.findIndex y p) (Valid.index {t = p} vp j)
  ∙ cong (λ y → P.findIndex y p) (castFin-value (sym (Valid.len {t = p} vp)) j)

inverse-hit : {n : ℕ} (p : P.Table) (vp : P.isPerm n p ≡ true) (j : Fin n)
  → P.apply p (P.findIndex (toℕ j) p) ≡ toℕ j
inverse-hit p vp j =
  cong (P.apply p) (sym (w .snd .fst))
  ∙ at-nth (P.length p) p (w .fst) ∙ w .snd .snd
  where
  w = findIndex-witness (toℕ j) p
    (member-complete _≡ᵇ_ natEq-refl (Valid.backward {t = p} vp _ (range-member j)))

equivalence-injective : {X Y : Type} (e : X ≃ Y) {x y : X} → e .fst x ≡ e .fst y → x ≡ y
equivalence-injective e {x} {y} p = sym (retEq e x) ∙ cong (invEq e) p ∙ retEq e y

tablePermutation-inverse : {n : ℕ} (p : P.Table)
  (vp : P.isPerm n p ≡ true) (vi : P.isPerm n (P.inverse p) ≡ true)
  → tablePermutation {t = P.inverse p} vi ≡ invEquiv (tablePermutation {t = p} vp)
tablePermutation-inverse p vp vi = equivEq (funExt λ j → equivalence-injective (tablePermutation {t = p} vp)
  (toℕ-injective
    (tablePermutation-value {t = p} vp (tablePermutation {t = P.inverse p} vi .fst j)
     ∙ cong (P.apply p) (tablePermutation-value {t = P.inverse p} vi j ∙ inverse-apply p vp j)
     ∙ inverse-hit p vp j)
   ∙ sym (secEq (tablePermutation {t = p} vp) j)))

open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Data.Nat using (znots; snotz; injSuc)

certificatePermutation-compose : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
  (vpq : P.isPerm n (P.compose p q) ≡ true)
  → certificatePermutation {t = P.compose p q} vpq
    ≡ compEquiv (certificatePermutation {t = p} vp) (certificatePermutation {t = q} vq)
certificatePermutation-compose {n} p q vp vq vpq =
  cong invEquiv (tablePermutation-compose p q vp vq vpq)
  ∙ GroupTheory.invDistr (FinSymGroup n)
      (tablePermutation {t = q} vq) (tablePermutation {t = p} vp)

certificatePermutation-inverse : {n : ℕ} (p : P.Table)
  (vp : P.isPerm n p ≡ true) (vi : P.isPerm n (P.inverse p) ≡ true)
  → certificatePermutation {t = P.inverse p} vi ≡ invEquiv (certificatePermutation {t = p} vp)
certificatePermutation-inverse p vp vi = cong invEquiv (tablePermutation-inverse p vp vi)

nth-range : {n : ℕ} (d : ℕ) (i : Fin n) → P.nth d (P.range n) (toℕ i) ≡ toℕ i
nth-range {suc n} d fzero = refl
nth-range {suc n} d (fsuc i) = nth-map-range d suc i

tablePermutation-identity : (n : ℕ) (v : P.isPerm n (P.identity n) ≡ true)
  → tablePermutation {t = P.identity n} v ≡ idEquiv (Fin n)
tablePermutation-identity n v = equivEq (funExt λ i → toℕ-injective
  (tablePermutation-value {t = P.identity n} v i ∙ nth-range (P.length (P.range n)) i))

certificatePermutation-identity : (n : ℕ) (v : P.isPerm n (P.identity n) ≡ true)
  → certificatePermutation {t = P.identity n} v ≡ idEquiv (Fin n)
certificatePermutation-identity n v = cong invEquiv (tablePermutation-identity n v)
  ∙ invEquivIdEquiv (Fin n)

listEq-sound : (eq : A → A → Bool)
  → ((x y : A) → eq x y ≡ true → x ≡ y)
  → (xs ys : List A) → P.listEq eq xs ys ≡ true → xs ≡ ys
listEq-sound eq sound [] [] v = refl
listEq-sound eq sound [] (y ∷ ys) v = Empty.rec (false≢true v)
listEq-sound eq sound (x ∷ xs) [] v = Empty.rec (false≢true v)
listEq-sound eq sound (x ∷ xs) (y ∷ ys) v =
  cong₂ _∷_ (sound x y (and-left v)) (listEq-sound eq sound xs ys (and-right v))

tableEq-sound : (p q : P.Table) → P.tableEq p q ≡ true → p ≡ q
tableEq-sound = listEq-sound _≡ᵇ_ natEq-sound

listEq-refl : (eq : A → A → Bool) → ((x : A) → eq x x ≡ true)
  → (xs : List A) → P.listEq eq xs xs ≡ true
listEq-refl eq r [] = refl
listEq-refl eq r (x ∷ xs) = cong₂ _and_ (r x) (listEq-refl eq r xs)

tableEq-refl : (t : P.Table) → P.tableEq t t ≡ true
tableEq-refl = listEq-refl _≡ᵇ_ natEq-refl

nth-ext : (n dp dq : ℕ) (p q : P.Table) → P.length p ≡ n → P.length q ≡ n
  → ((i : Fin n) → P.nth dp p (toℕ i) ≡ P.nth dq q (toℕ i)) → p ≡ q
nth-ext zero dp dq [] [] lp lq e = refl
nth-ext zero dp dq [] (_ ∷ _) lp lq e = Empty.rec (snotz lq)
nth-ext zero dp dq (_ ∷ _) q lp lq e = Empty.rec (snotz lp)
nth-ext (suc n) dp dq [] q lp lq e = Empty.rec (znots lp)
nth-ext (suc n) dp dq (_ ∷ _) [] lp lq e = Empty.rec (znots lq)
nth-ext (suc n) dp dq (x ∷ xs) (y ∷ ys) lp lq e =
  cong₂ _∷_ (e fzero) (nth-ext n dp dq xs ys (injSuc lp) (injSuc lq) (λ i → e (fsuc i)))

tablePermutation-injective : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
  → tablePermutation {t = p} vp ≡ tablePermutation {t = q} vq → p ≡ q
tablePermutation-injective {n} p q vp vq e = nth-ext n (P.length p) (P.length q) p q
  (Valid.len {t = p} vp) (Valid.len {t = q} vq)
  (λ i → sym (tablePermutation-value {t = p} vp i)
    ∙ cong (λ e → toℕ (e .fst i)) e ∙ tablePermutation-value {t = q} vq i)

certificatePermutation-injective : {n : ℕ} (p q : P.Table)
  (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
  → certificatePermutation {t = p} vp ≡ certificatePermutation {t = q} vq → p ≡ q
certificatePermutation-injective {n} p q vp vq e = tablePermutation-injective p q vp vq
  (sym (GroupTheory.invInv (FinSymGroup n) (tablePermutation {t = p} vp))
   ∙ cong invEquiv e ∙ GroupTheory.invInv (FinSymGroup n) (tablePermutation {t = q} vq))
