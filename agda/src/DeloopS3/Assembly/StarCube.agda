{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.StarCube where

-- Second descent, with its seam strictified relative
-- to BOTH vertices.  All selected fibres use the O-side basepoint.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)
open import Cubical.Foundations.Path using (compPathrEquiv)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd)
open import Cubical.HITs.Pushout.Base using (Pushout; inl; inr; push)
import DeloopS3.Sphere.TruncationCartesian as TC
import DeloopS3.Assembly.CartesianPushout as CP
open import DeloopS3.Assembly.LocalCubes public

EO EI PO PI : Type
EO = E octa
EI = E icosa
PO = P octa
PI = P icosa

E* P* : Type
E* = Pushout {A = R} {B = EO} {C = EI} (iG octa) (iG icosa)
P* = Pushout {A = N} {B = PO} {C = PI} (nG octa) (nG icosa)

kEO : EO → E*
kEO = inl {f = iG octa} {g = iG icosa}

kEI : EI → E*
kEI = inr {f = iG octa} {g = iG icosa}

kPO : PO → P*
kPO = inl {f = nG octa} {g = nG icosa}

kPI : PI → P*
kPI = inr {f = nG octa} {g = nG icosa}

module StarRaw = CP.CartesianPushout
  {ℓ = ℓ-zero} {A = R} {B = EO} {C = EI}
  {A' = N} {B' = PO} {C' = PI}
  (iG octa) (iG icosa) (nG octa) (nG icosa)
  u (t octa) (t icosa) (λ _ → refl) (λ _ → refl)
  (restriction-G octa) (restriction-G icosa)

t* : E* → P*
t* (inl x) = kPO (t octa x)
t* (inr y) = kPI (t icosa y)
t* (push r i) = push {f = nG octa} {g = nG icosa} (u r) i

private
  abstract
    -- _∙_ is right-associative: remove the left unit, then the right one.
    unit-seam : ∀ {ℓ} {X : Type ℓ} {x y : X} (s : x ≡ y)
      → refl ∙ s ∙ refl ≡ s
    unit-seam s = sym (lUnit (s ∙ refl)) ∙ sym (rUnit s)

  strictification-at : (x : E*) → StarRaw.t x ≡ t* x
  strictification-at (inl x) = refl
  strictification-at (inr y) = refl
  strictification-at (push r i) j =
    unit-seam (push {f = nG octa} {g = nG icosa} (u r)) j i

-- Transparent on the vertices: the transports below keep comm = refl.
strictification : StarRaw.t ≡ t*
strictification = funExt strictification-at

abstract
  star-left : TC.CartSquare kEO kPO (t octa) t* (λ _ → refl)
  star-left = transport
    (λ j → TC.CartSquare kEO kPO (t octa) (strictification j) (λ _ → refl))
    StarRaw.descend-left

  star-right : TC.CartSquare kEI kPI (t icosa) t* (λ _ → refl)
  star-right = transport
    (λ j → TC.CartSquare kEI kPI (t icosa) (strictification j) (λ _ → refl))
    StarRaw.descend-right

e*₀ : E*
e*₀ = kEO (eG₀ octa)

p*₀ : P*
p*₀ = kPO (pG₀ octa)

aO : kEO (eG₀ octa) ≡ e*₀
aO = refl

bO : kPO (pG₀ octa) ≡ p*₀
bO = refl

aI : kEI (eG₀ icosa) ≡ e*₀
aI = sym (push {f = iG octa} {g = iG icosa} r₀)

bI : kPI (pG₀ icosa) ≡ p*₀
bI = sym (push {f = nG octa} {g = nG icosa} n₀)

-- The I-side pointing is the reversed seam, not refl.
aI-coherence : cong t* aI ≡ bI
aI-coherence = refl

UO : fiber (t octa) (pG₀ octa) → fiber t* p*₀
UO (x , s) = kEO x , cong kPO s

UI : fiber (t icosa) (pG₀ icosa) → fiber t* p*₀
UI (x , s) = kEI x , cong kPI s ∙ bI

λ* : F → fiber t* p*₀
λ* (r , s) = kEO (iG octa r) , cong (kPO ∘ nG octa) s

private
  -- The same concrete fibre maps throughout the relative strictification.
  λO-family : (j : I) → fiber (t octa) (pG₀ octa)
    → fiber (strictification j) p*₀
  λO-family j (x , s) = kEO x , cong kPO s

  λI-family : (j : I) → fiber (t icosa) (pG₀ icosa)
    → fiber (strictification j) (kPI (pG₀ icosa))
  λI-family j (x , s) = kEI x , cong kPI s

  abstract
    λI-vertex-isEquiv : isEquiv (λI-family i1)
    λI-vertex-isEquiv = transport
      (λ j → isEquiv (λI-family j)) (StarRaw.λC-isEquiv (pG₀ icosa))

  reindex-I : fiber t* (kPI (pG₀ icosa)) ≃ fiber t* p*₀
  reindex-I = Σ-cong-equiv-snd
    {A = E*} {B = λ x → t* x ≡ kPI (pG₀ icosa)}
    {B' = λ x → t* x ≡ p*₀}
    (λ x → compPathrEquiv {x = t* x} bI)

abstract
  UO-isEquiv : isEquiv UO
  UO-isEquiv = transport
    (λ j → isEquiv (λO-family j)) (StarRaw.λB-isEquiv (pG₀ octa))

  UI-isEquiv : isEquiv UI
  UI-isEquiv = snd (compEquiv
    {A = fiber (t icosa) (pG₀ icosa)}
    {B = fiber t* (kPI (pG₀ icosa))} {C = fiber t* p*₀}
    (λI-family i1 , λI-vertex-isEquiv) reindex-I)

  λ*-isEquiv : isEquiv λ*
  λ*-isEquiv = snd (compEquiv
    {A = F} {B = fiber (t octa) (pG₀ octa)} {C = fiber t* p*₀}
    (local-fibre octa) (UO , UO-isEquiv))
