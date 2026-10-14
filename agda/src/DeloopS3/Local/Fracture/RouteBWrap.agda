{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.RouteBWrap where

-- Fibre and loop comparisons for localization over simply connected bases,
-- with specified unit homotopies. This is not arbitrary pullback stability;
-- the loop comparison specializes RouteB2.path-comparison-isEquiv.
open import DeloopS3.Local.Base
open import DeloopS3.Local.Powers
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.RouteB2 using
  (SC ; L-map ; fiber-unit ; fiber-comparison ; fiber-comparison-β ;
   localization-preserves-fiber ; path-comparison ; path-comparison-β ;
   path-comparison-isEquiv ; L∙ ; η∙ ; loop-comparison ; unit-loop-normalize)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations public
  using (PB ; module Square)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
import Cubical.HITs.Localization.Properties as Loc

-- The uncurried square interface; all four corner types can be
-- supplied explicitly without unfolding a localization proof.
Cartesian : {A A' B B' : Type}
  (u : A → A') (f : A → B) (f' : A' → B') (v : B → B')
  → ((a : A) → f' (u a) ≡ v (f a)) → Type
Cartesian {A} {A'} {B} {B'} = Square.Cartesian A A' B B'

private
  -- Ordinary reflector UP, independent of the Route B implementation.
  unit-local-isEquiv : (r : ℕ) (A : Type)
    → Local r A → isEquiv (η {r} {A})
  unit-local-isEquiv r A lA = isoToIsEquiv
    (iso (η {r} {A}) inverse sec-law (λ _ → refl))
    where
    inverse : L r A → A
    inverse = Loc.rec {F = F r} {X = A} {Y = A} lA (idfun A)

    sec-law : (z : L r A) → η {r} {A} (inverse z) ≡ z
    sec-law = Unique.≡onη {F = F r} {X = A} {Y = L r A}
      (local-L r A) (η {r} {A} ∘ inverse) (idfun (L r A)) (λ _ → refl)

-- The ACTUAL fibre map of the unit square is a composite of two
-- equivalences.  The comparison's β rule specifies its map on generators.
abstract
  local-fibre-unit-isEquiv : (r : ℕ) {E B : Type} (f : E → B)
    → SC B → (b : B) → Local r (fiber f b)
    → isEquiv (fiber-unit r {E = E} {B = B} f b)
  local-fibre-unit-isEquiv r {E} {B} f sc b local =
    subst isEquiv
      (funExt (fiber-comparison-β r {E = E} {B = B} f b))
      (snd (compEquiv
        (η {r} {fiber f b} , unit-local-isEquiv r (fiber f b) local)
        (fiber-comparison r {E = E} {B = B} f b ,
          localization-preserves-fiber r {E = E} {B = B} f b sc)))

  local-fibres-unit-cartesian : (r : ℕ) {E B : Type} (f : E → B)
    → SC B → ((b : B) → Local r (fiber f b))
    → Cartesian {A = E} {A' = L r E} {B = B} {B' = L r B}
        (η {r} {E}) f (L-map r {A = E} {B = B} f) (η {r} {B})
        (λ _ → refl)
  local-fibres-unit-cartesian r {E} {B} f sc local =
    Square.fiberwise→cartesian E (L r E) B (L r B)
      (η {r} {E}) f (L-map r {A = E} {B = B} f) (η {r} {B})
      (λ _ → refl) λ b →
        subst isEquiv
          (funExt λ { (e , p) i → η {r} {E} e , lUnit (cong (η {r} {B}) p) i })
          (local-fibre-unit-isEquiv r {E = E} {B = B} f sc b (local b))

-- The finite power-square instance.  Power-fibre arithmetic supplies the
-- displayed fibre locality premise; this implication uses no coprime arithmetic.
localize-power-square : (r s : ℕ) (X : Pointed ℓ-zero)
  → SC (typ (Ω X))
  → ((p : typ (Ω X)) → Local r (fiber (powLoop {X = typ X} {x = pt X} s) p))
  → Cartesian
      {A = typ (Ω X)} {A' = L r (typ (Ω X))}
      {B = typ (Ω X)} {B' = L r (typ (Ω X))}
      (η {r} {typ (Ω X)}) (powLoop {X = typ X} {x = pt X} s)
      (L-map r {A = typ (Ω X)} {B = typ (Ω X)} (powLoop {X = typ X} {x = pt X} s))
      (η {r} {typ (Ω X)}) (λ _ → refl)
localize-power-square r s X = local-fibres-unit-cartesian r
  {E = typ (Ω X)} {B = typ (Ω X)} (powLoop {X = typ X} {x = pt X} s)

-- Raw based-path equivalence, with X and both endpoints explicit at the
-- stable Route B boundary.  Its carrier has the strict unit computation.
loop-path-equivalence : (r : ℕ) (X : Type) → SC X → (x : X)
  → L r (x ≡ x) ≃ (η {r} {X} x ≡ η {r} {X} x)
loop-path-equivalence r X sc x =
  path-comparison r {X = X} x x , path-comparison-isEquiv r {X = X} sc x x

loop-path-equivalence-β : (r : ℕ) (X : Type) (sc : SC X) (x : X) (p : x ≡ x)
  → equivFun (loop-path-equivalence r X sc x) (η {r} {x ≡ x} p)
      ≡ cong (η {r} {X}) p
loop-path-equivalence-β r X sc x p = path-comparison-β r {X = X} x x p

-- Extend the specified power naturality homotopy, not merely its
-- existence.  This equality needs no connectivity; SC makes κ an equivalence.
loop-power-homotopy : (r s : ℕ) (X : Pointed ℓ-zero)
  → loop-comparison r X ∘
      L-map r {A = typ (Ω X)} {B = typ (Ω X)} (powLoop {X = typ X} {x = pt X} s)
    ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s ∘ loop-comparison r X
loop-power-homotopy r s X = funExt
  (Unique.≡onη {F = F r} {X = typ (Ω X)} {Y = typ (Ω (L∙ r X))}
    (local-path {m = r} {X = L r (typ X)} (local-L r (typ X))
      (η {r} {typ X} (pt X)) (η {r} {typ X} (pt X)))
    (loop-comparison r X ∘
      L-map r {A = typ (Ω X)} {B = typ (Ω X)} (powLoop {X = typ X} {x = pt X} s))
    (powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s ∘ loop-comparison r X)
    (cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s))

loop-power-β : (r s : ℕ) (X : Pointed ℓ-zero) (p : typ (Ω X))
  → funExt⁻ (loop-power-homotopy r s X) (η {r} {typ (Ω X)} p)
      ≡ cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s p
loop-power-β r s X p = refl

-- The connectivity-bearing loop-power comparison, retaining the same β.
localize-loop-power : (r s : ℕ) (X : Pointed ℓ-zero) → SC (typ X)
  → loop-comparison r X ∘
      L-map r {A = typ (Ω X)} {B = typ (Ω X)} (powLoop {X = typ X} {x = pt X} s)
    ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s ∘ loop-comparison r X
localize-loop-power r s X sc = loop-power-homotopy r s X

localize-loop-power-β : (r s : ℕ) (X : Pointed ℓ-zero) (sc : SC (typ X))
  (p : typ (Ω X))
  → funExt⁻ (localize-loop-power r s X sc) (η {r} {typ (Ω X)} p)
      ≡ cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s p
localize-loop-power-β r s X sc p = refl

-- Ω→ includes pointing conjugations.  Transport the raw naturality square
-- along unit-loop-normalize, and retain the entire transport square.
-- Thus the marked homotopy above is not discarded upon passing to Ωη.
unit-loop-power-square : (r s : ℕ) (X : Pointed ℓ-zero) (p : typ (Ω X))
  → fst (Ω→ (η∙ r X)) (powLoop {X = typ X} {x = pt X} s p)
      ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s (fst (Ω→ (η∙ r X)) p)
unit-loop-power-square r s X p = transport
  (λ i → unit-loop-normalize r X (powLoop {X = typ X} {x = pt X} s p) (~ i)
    ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s
        (unit-loop-normalize r X p (~ i)))
  (cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s p)

unit-loop-power-square-normalize : (r s : ℕ) (X : Pointed ℓ-zero) (p : typ (Ω X))
  → PathP
      (λ i → unit-loop-normalize r X (powLoop {X = typ X} {x = pt X} s p) i
        ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s
            (unit-loop-normalize r X p i))
      (unit-loop-power-square r s X p)
      (cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s p)
unit-loop-power-square-normalize r s X p = symP (transport-filler
  (λ i → unit-loop-normalize r X (powLoop {X = typ X} {x = pt X} s p) (~ i)
    ≡ powLoop {X = L r (typ X)} {x = η {r} {typ X} (pt X)} s
        (unit-loop-normalize r X p (~ i)))
  (cong-powLoop {X = typ X} {Y = L r (typ X)} (η {r} {typ X}) s p))
