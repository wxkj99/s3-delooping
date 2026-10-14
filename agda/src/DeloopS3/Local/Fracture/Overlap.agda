{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Overlap where

-- Product locality and the equivalence of iterated localizations.
-- No coprimality is used.  Only preservation of the other locality and
-- the resulting overlap equivalence require simple connectedness.
open import DeloopS3.Local.Base
open import DeloopS3.Local.Powers
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.EI using (powLoop-· ; local-factor)
open import DeloopS3.Local.RouteB1.Closure using (local-prop)
open import DeloopS3.Local.RouteB2 using
  (Conn ; SC ; L-map ; L∙ ; L-preserves-SC ; connected-mere-path)
open import DeloopS3.Local.Fracture.RouteBWrap using (loop-path-equivalence)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using
  (isEquiv[f∘equivFunA≃B]→isEquiv[f])
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels using
  (isProp× ; isProp→isOfHLevelSuc)
open import Cubical.Data.Nat using (ℕ ; _·_ ; ·-comm)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Homotopy.Connected using (isConnectedSubtr)
import Cubical.HITs.Localization.Properties as Loc
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as Tr

-- Commuting factors give the forward implication; composition of the
-- two power equivalences gives the reverse implication.  Both are props.
product-locality : (m n : ℕ) (A : Type)
  → Local (m · n) A ≃ (Local m A × Local n A)
product-locality m n A = propBiimpl→Equiv
  (local-prop {m = m · n} {A = A})
  (isProp× (local-prop {m = m} {A = A})
           (local-prop {m = n} {A = A})) split combine
  where
  split : Local (m · n) A → Local m A × Local n A
  split lA =
    local-factor {m = m · n} {d = m} {b = n} {Z = A} refl lA ,
    local-factor {m = m · n} {d = n} {b = m} {Z = A} (·-comm n m) lA

  combine : Local m A × Local n A → Local (m · n) A
  combine (lm , ln) = powers→local {X = A} {m = m · n} λ a →
    subst isEquiv (funExt (powLoop-· {X = A} {x = a} m n))
      (snd (compEquiv
        (powLoop {X = A} {x = a} n , local→powers {X = A} {m = n} ln a)
        (powLoop {X = A} {x = a} m , local→powers {X = A} {m = m} lm a)))

private
  -- Ordinary UP: apply L to an inverse, and extend the inverse laws by
  -- uniqueness.  Endpoint types are explicit to avoid HIT unification.
  L-map-isEquiv : (m : ℕ) (A B : Type) (f : A → B)
    → isEquiv f → isEquiv (L-map m {A = A} {B = B} f)
  L-map-isEquiv m A B f ef = isoToIsEquiv
    (iso forward backward sec-law ret-law)
    where
    e : A ≃ B
    e = f , ef

    forward : L m A → L m B
    forward = L-map m {A = A} {B = B} f

    backward : L m B → L m A
    backward = L-map m {A = B} {B = A} (invEq e)

    sec-law : (b : L m B) → forward (backward b) ≡ b
    sec-law = Unique.≡onη {F = F m} {X = B} {Y = L m B}
      (local-L m B) (forward ∘ backward) (idfun (L m B))
      (λ b → cong (η {m} {B}) (secEq e b))

    ret-law : (a : L m A) → backward (forward a) ≡ a
    ret-law = Unique.≡onη {F = F m} {X = A} {Y = L m A}
      (local-L m A) (backward ∘ forward) (idfun (L m A))
      (λ a → cong (η {m} {A}) (retEq e a))

  based-powers→local : (n : ℕ) (X : Pointed ℓ-zero)
    → Conn (typ X) → isEquiv (powLoop {X = typ X} {x = pt X} n)
    → Local n (typ X)
  based-powers→local n X conn power = powers→local {X = typ X} {m = n} λ x →
    PT.rec (isPropIsEquiv (powLoop {X = typ X} {x = x} n))
      (λ p → subst (λ y → isEquiv (powLoop {X = typ X} {x = y} n)) p power)
      (connected-mere-path {A = typ X} conn (pt X) x)

  -- Keep the two-out-of-three calculation generic, so elaboration need
  -- not normalize the proof of the large Route B comparison equivalence.
  abstract
    power-via-comparison : (U V : Type) (k : U → V)
      (f : U → U) (g : V → V) → isEquiv k → isEquiv f
      → k ∘ f ≡ g ∘ k → isEquiv g
    power-via-comparison U V k f g ek ef h =
      isEquiv[f∘equivFunA≃B]→isEquiv[f] {A = U} {B = V} {C = V} g (k , ek)
        (subst (isEquiv {A = U} {B = V}) h
          (snd (compEquiv (f , ef) (k , ek))))

  -- Use the raw F2 carrier throughout this specialization.  In particular,
  -- no conversion against a pointed-loop specialization is needed.
  module LocalizedPower (m n : ℕ) (A : Type) (a : A)
    (sc : SC A) (ln : Local n A) where
    U = L m (a ≡ a)
    V = η {m} {A} a ≡ η {m} {A} a

    comparison : U ≃ V
    comparison = loop-path-equivalence m A sc a

    k : U → V
    k = equivFun comparison

    f : U → U
    f = L-map m {A = a ≡ a} {B = a ≡ a} (powLoop {X = A} {x = a} n)

    g : V → V
    g = powLoop {X = L m A} {x = η {m} {A} a} n

    ef : isEquiv f
    ef = L-map-isEquiv m (a ≡ a) (a ≡ a) (powLoop {X = A} {x = a} n)
      (local→powers {X = A} {m = n} ln a)

    h : k ∘ f ≡ g ∘ k
    h = Unique.unique {F = F m} {X = a ≡ a} {Y = V}
      (local-path {m = m} {X = L m A} (local-L m A)
        (η {m} {A} a) (η {m} {A} a))
      (k ∘ f) (g ∘ k)
      (λ p → cong-powLoop {X = A} {Y = L m A} (η {m} {A}) n {x = a} p)

    result : isEquiv g
    result = power-via-comparison U V k f g (snd comparison) ef h

  localized-based-power : (m n : ℕ) (A : Type) (a : A)
    → SC A → Local n A
    → isEquiv (powLoop {X = L m A} {x = η {m} {A} a} n)
  localized-based-power m n A a sc ln = LocalizedPower.result m n A a sc ln

-- The loop comparison transports the localized power equivalence.
-- Connectedness propagates it from the chosen point.  Mere inhabitance
-- suffices to choose that point because locality is a proposition.
abstract
  localize-preserves-other-local : (m n : ℕ) {A : Type}
    → SC A → Local n A → Local n (L m A)
  localize-preserves-other-local m n {A} sc ln =
    PT.rec (local-prop {m = n} {A = L m A}) pointed inhabited
    where
    pointed : A → Local n (L m A)
    pointed a = based-powers→local n (L∙ m (A , a))
      (isConnectedSubtr {A = L m A} 2 1 (L-preserves-SC m {X = A} sc))
      (localized-based-power m n A a sc ln)

    inhabited : PT.∥ A ∥₁
    inhabited = Tr.rec (isProp→isOfHLevelSuc 2 PT.squash₁) PT.∣_∣₁ (fst sc)

private
  module Overlap (m n : ℕ) (A : Type) (sc : SC A) where
    Iter = L m (L n A)
    P = L (m · n) A

    local-m-I : Local m Iter
    local-m-I = local-L m (L n A)

    local-n-I : Local n Iter
    local-n-I = localize-preserves-other-local m n {A = L n A}
      (L-preserves-SC n {X = A} sc) (local-L n A)

    local-mn-I : Local (m · n) Iter
    local-mn-I = invEq (product-locality m n Iter) (local-m-I , local-n-I)

    local-m-P : Local m P
    local-m-P = fst (equivFun (product-locality m n P) (local-L (m · n) A))

    local-n-P : Local n P
    local-n-P = snd (equivFun (product-locality m n P) (local-L (m · n) A))

    inner : L n A → P
    inner = Loc.rec {F = F n} {X = A} {Y = P} local-n-P (η {m · n} {A})

    forward : Iter → P
    forward = Loc.rec {F = F m} {X = L n A} {Y = P} local-m-P inner

    backward : P → Iter
    backward = Loc.rec {F = F (m · n)} {X = A} {Y = Iter} local-mn-I
      (η {m} {L n A} ∘ η {n} {A})

    sec-law : (p : P) → forward (backward p) ≡ p
    sec-law = Unique.≡onη {F = F (m · n)} {X = A} {Y = P}
      (local-L (m · n) A) (forward ∘ backward) (idfun P) (λ _ → refl)

    ret-law : (t : Iter) → backward (forward t) ≡ t
    ret-law = Unique.≡onη {F = F m} {X = L n A} {Y = Iter}
      local-m-I (backward ∘ forward) (idfun Iter)
      (Unique.≡onη {F = F n} {X = A} {Y = Iter}
        local-n-I (backward ∘ inner) (η {m} {L n A}) (λ _ → refl))

-- Successive restriction along the units is the ordinary UP for the
-- product-local target.  The two inverse laws above apply uniqueness
-- once on L_(mn), and twice on L_m L_n, respectively.
iterated-localization : (m n : ℕ) {A : Type}
  → SC A → L m (L n A) ≃ L (m · n) A
iterated-localization m n {A} sc = isoToEquiv
  (iso (Overlap.forward m n A sc) (Overlap.backward m n A sc)
    (Overlap.sec-law m n A sc) (Overlap.ret-law m n A sc))

iterated-localization-β : (m n : ℕ) {A : Type} (sc : SC A) (a : A)
  → equivFun (iterated-localization m n {A = A} sc)
      (η {m} {L n A} (η {n} {A} a)) ≡ η {m · n} {A} a
iterated-localization-β m n sc a = refl
