{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Powers where

-- The free-loop and path arguments are ported
-- from Loc.Local / Loc.LoopSquareLocal, with induction on arbitrary m.
open import DeloopS3.Local.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.HalfAdjoint using (congIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Functions.FunExtEquiv using (funExtIso)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (ΣPathP ; Σ-cong-equiv-snd)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Susp.Base using (Susp ; north ; south ; merid ; suspFun)
open import Cubical.HITs.Susp.Properties using (funSpaceSuspIso)

cong-powLoop : {X Y : Type} (g : X → Y) (m : ℕ)
  {x : X} (p : x ≡ x) → cong g (powLoop m p) ≡ powLoop m (cong g p)
cong-powLoop g zero p = refl
cong-powLoop g (suc m) p = cong-∙ g p (powLoop m p)
  ∙ cong (cong g p ∙_) (cong-powLoop g m p)

module _ {X : Type} where
  freeIso : Iso (S¹ → X) (Σ[ x ∈ X ] x ≡ x)
  Iso.fun freeIso g = g base , cong g loop
  Iso.inv freeIso (x , p) base = x
  Iso.inv freeIso (x , p) (loop i) = p i
  Iso.sec freeIso (x , p) = refl
  Iso.ret freeIso g = funExt λ { base → refl ; (loop i) → refl }

  local→powers : ∀ {m} → Local m X
    → (x : X) → isEquiv (powLoop {x = x} m)
  local→powers {m} lX = fiberEquiv (λ x → x ≡ x) (λ x → x ≡ x)
    (λ x → powLoop {x = x} m) totalEquiv
    where
    totalPower : (Σ[ x ∈ X ] x ≡ x) → (Σ[ x ∈ X ] x ≡ x)
    totalPower (x , p) = x , powLoop m p

    conjugate = compEquiv (isoToEquiv (invIso freeIso))
      (compEquiv ((λ g → g ∘ deg₁ m) , local→preEquiv lX)
        (isoToEquiv freeIso))

    agrees : fst conjugate ≡ totalPower
    agrees = funExt λ { (x , p) →
      ΣPathP (refl , cong-powLoop (Iso.inv freeIso (x , p)) m loop) }

    totalEquiv : isEquiv totalPower
    totalEquiv = subst isEquiv agrees (snd conjugate)

  powers→local : ∀ {m}
    → ((x : X) → isEquiv (powLoop {x = x} m)) → Local m X
  powers→local {m} powers = preEquiv→local
    (subst isEquiv (funExt agrees) (snd conjugate))
    where
    total : (Σ[ x ∈ X ] x ≡ x) ≃ (Σ[ x ∈ X ] x ≡ x)
    total = Σ-cong-equiv-snd (λ x → powLoop m , powers x)

    conjugate : (S¹ → X) ≃ (S¹ → X)
    conjugate = compEquiv (isoToEquiv freeIso)
      (compEquiv total (isoToEquiv (invIso freeIso)))

    agrees : (g : S¹ → X) → fst conjugate g ≡ g ∘ deg₁ m
    agrees g = cong (Iso.inv freeIso)
      (ΣPathP (refl , sym (cong-powLoop g m loop)))
      ∙ Iso.ret freeIso (g ∘ deg₁ m)

local-path : ∀ {m X} → Local m X → (x y : X) → Local m (x ≡ y)
local-path {m} {X} lX x y = preEquiv→local (isoToIsEquiv pathIso)
  where
  pre : (S¹ → X) → (S¹ → X)
  pre g = g ∘ deg₁ m

  pathIso : Iso (S¹ → x ≡ y) (S¹ → x ≡ y)
  pathIso = compIso
    (compIso funExtIso (congIso (equivToIso (pre , local→preEquiv lX))))
    (invIso funExtIso)

SphereFromCircle : ℕ → Type
SphereFromCircle zero = S¹
SphereFromCircle (suc n) = Susp (SphereFromCircle n)

degSphere : (m n : ℕ) → SphereFromCircle n → SphereFromCircle n
degSphere m zero = deg₁ m
degSphere m (suc n) = suspFun (degSphere m n)

-- The suspension mapping-space description, over each pair of poles.
susp-preEquiv : {A B Z : Type} (f : A → B)
  → ((x y : Z) → isEquiv (λ (g : B → x ≡ y) → g ∘ f))
  → isEquiv (λ (g : Susp B → Z) → g ∘ suspFun f)
susp-preEquiv {A} {B} {Z} f paths =
  subst isEquiv (funExt agrees) (snd conjugate)
  where
  total : (Σ[ x ∈ Z ] Σ[ y ∈ Z ] (B → x ≡ y))
    ≃ (Σ[ x ∈ Z ] Σ[ y ∈ Z ] (A → x ≡ y))
  total = Σ-cong-equiv-snd λ x → Σ-cong-equiv-snd λ y →
    (λ g → g ∘ f) , paths x y

  conjugate : (Susp B → Z) ≃ (Susp A → Z)
  conjugate = compEquiv (isoToEquiv (invIso funSpaceSuspIso))
    (compEquiv total (isoToEquiv funSpaceSuspIso))

  agrees : (g : Susp B → Z) → fst conjugate g ≡ g ∘ suspFun f
  agrees g = funExt λ { north → refl ; south → refl ; (merid a i) → refl }

local-sphere : ∀ {m Z} → Local m Z → (n : ℕ)
  → isEquiv (λ (f : SphereFromCircle n → Z) → f ∘ degSphere m n)
local-sphere lZ zero = local→preEquiv lZ
local-sphere {m} lZ (suc n) = susp-preEquiv (degSphere m n)
  (λ x y → local-sphere (local-path lZ x y) n)
