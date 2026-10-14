{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB1.Closure where

-- Universe-polymorphic locality, closure properties, and mapping-space fibres.
-- Base.Local is intentionally left small; Localᵘ reduces to it on Type.
open import DeloopS3.Local.Base using (F ; deg₁)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using
  (congEquiv ; isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Equiv.PathSplit using
  (toIsEquiv ; fromIsEquiv ; isPropIsPathSplitEquiv)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using
  (Σ-cong-equiv ; Σ-cong-equiv-snd ; Σ-Π-≃ ; ΣPathTransport≃PathΣ)
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.S1.Properties using (isConnectedS¹)
import Cubical.HITs.Localization.Base as Localization
import Cubical.HITs.PropositionalTruncation as PT

Localᵘ : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
Localᵘ m A = Localization.isLocal (F m) A

Separated : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
Separated m A = (a b : A) → Localᵘ m (a ≡ b)

localᵘ→preEquiv : ∀ {ℓ m} {A : Type ℓ} → Localᵘ m A
  → isEquiv (λ (g : S¹ → A) → g ∘ deg₁ m)
localᵘ→preEquiv h = toIsEquiv _ (h tt)

preEquiv→localᵘ : ∀ {ℓ m} {A : Type ℓ}
  → isEquiv (λ (g : S¹ → A) → g ∘ deg₁ m) → Localᵘ m A
preEquiv→localᵘ h _ = fromIsEquiv _ h

local-prop : ∀ {ℓ m} {A : Type ℓ} → isProp (Localᵘ m A)
local-prop = isPropΠ λ _ → isPropIsPathSplitEquiv _

local-equiv : ∀ {ℓ ℓ' m} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → Localᵘ m A → Localᵘ m B
local-equiv {m = m} {A = A} {B = B} e lA = preEquiv→localᵘ
  (subst isEquiv agrees (snd conjugate))
  where
  post : Iso (S¹ → A) (S¹ → B)
  Iso.fun post h = fst e ∘ h
  Iso.inv post h = invEq e ∘ h
  Iso.sec post h = funExt λ s → secEq e (h s)
  Iso.ret post h = funExt λ s → retEq e (h s)

  conjugate : (S¹ → B) ≃ (S¹ → B)
  conjugate = compEquiv (isoToEquiv (invIso post))
    (compEquiv ((λ h → h ∘ deg₁ m) , localᵘ→preEquiv lA)
      (isoToEquiv post))

  agrees : fst conjugate ≡ (λ h → h ∘ deg₁ m)
  agrees = funExt λ h → funExt λ s → secEq e (h (deg₁ m s))

local-function : ∀ {ℓ ℓ' m} {A : Type ℓ} {B : Type ℓ'}
  → Localᵘ m B → Localᵘ m (A → B)
local-function {m = m} {A = A} {B = B} lB =
  preEquiv→localᵘ (isoToIsEquiv pointwise)
  where
  preB : (S¹ → B) ≃ (S¹ → B)
  preB = (λ h → h ∘ deg₁ m) , localᵘ→preEquiv lB

  -- Currying makes precomposition pointwise precomposition into B.
  pointwise : Iso (S¹ → A → B) (S¹ → A → B)
  Iso.fun pointwise h = h ∘ deg₁ m
  Iso.inv pointwise h s a = invEq preB (λ t → h t a) s
  Iso.sec pointwise h = funExt λ s → funExt λ a →
    funExt⁻ (secEq preB (λ t → h t a)) s
  Iso.ret pointwise h = funExt λ s → funExt λ a →
    funExt⁻ (retEq preB (λ t → h t a)) s

-- The mapping-space fibre square for closure and dependent universal properties.
-- Its forward map is exactly restriction, including the path component.
module MappingFibres where
  restriction-equiv : ∀ {ℓX ℓY ℓA ℓB}
    {X : Type ℓX} {Y : Type ℓY} {A : Type ℓA} {B : Type ℓB}
    (u : X → Y) (f : A → B) (g : Y → B)
    → isEquiv (λ (h : Y → A) → h ∘ u)
    → isEquiv (λ (h : Y → B) → h ∘ u)
    → fiber (λ (h : Y → A) → f ∘ h) g
      ≃ fiber (λ (h : X → A) → f ∘ h) (g ∘ u)
  restriction-equiv u f g eA eB =
    Σ-cong-equiv ((λ h → h ∘ u) , eA)
      (λ h → congEquiv ((λ k → k ∘ u) , eB))

  maps-fiber-Iso : ∀ {ℓX ℓA ℓB}
    {X : Type ℓX} {A : Type ℓA} {B : Type ℓB}
    (f : A → B) (b : B)
    → Iso (X → fiber f b)
      (fiber (λ (h : X → A) → f ∘ h) (λ _ → b))
  Iso.fun (maps-fiber-Iso f b) h = (fst ∘ h) , funExt (snd ∘ h)
  Iso.inv (maps-fiber-Iso f b) (h , p) x = h x , funExt⁻ p x
  Iso.sec (maps-fiber-Iso f b) _ = refl
  Iso.ret (maps-fiber-Iso f b) _ = refl

local-fiber : ∀ {ℓ ℓ' m} {A : Type ℓ} {B : Type ℓ'}
  → Localᵘ m A → Localᵘ m B → (f : A → B) → (b : B)
  → Localᵘ m (fiber f b)
local-fiber {m = m} lA lB f b = preEquiv→localᵘ
  (isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ h → h ∘ deg₁ m)
    maps (snd (compEquiv maps restricted)))
  where
  maps = isoToEquiv (MappingFibres.maps-fiber-Iso {X = S¹} f b)
  restricted = MappingFibres.restriction-equiv (deg₁ m) f (λ _ → b)
    (localᵘ→preEquiv lA) (localᵘ→preEquiv lB)

-- Circle connectedness is used only to eliminate mere paths into props.
circle-prop-evaluation : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'}
  → ((a : A) → isProp (P a)) → (g : S¹ → A)
  → ((s : S¹) → P (g s)) ≃ P (g base)
circle-prop-evaluation {P = P} prop g = isoToEquiv evaluation
  where
  extend : P (g base) → (s : S¹) → P (g s)
  extend p s = PT.rec (prop (g s))
    (λ q → subst (P ∘ g) q p) (isConnectedS¹ s)

  evaluation : Iso ((s : S¹) → P (g s)) (P (g base))
  Iso.fun evaluation h = h base
  Iso.inv evaluation = extend
  Iso.sec evaluation p = prop (g base) _ _
  Iso.ret evaluation h = isPropΠ (λ s → prop (g s)) _ _

local-subtype : ∀ {ℓ ℓ' m} {A : Type ℓ} {P : A → Type ℓ'}
  → Localᵘ m A → ((a : A) → isProp (P a))
  → Localᵘ m (Σ A P)
local-subtype {m = m} {A = A} {P = P} lA prop = preEquiv→localᵘ
  (isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ h → h ∘ deg₁ m)
    maps (snd (compEquiv maps total)))
  where
  maps : (S¹ → Σ A P) ≃ (Σ[ g ∈ (S¹ → A) ] P (g base))
  maps = compEquiv Σ-Π-≃
    (Σ-cong-equiv-snd (circle-prop-evaluation prop))

  total : (Σ[ g ∈ (S¹ → A) ] P (g base))
    ≃ (Σ[ g ∈ (S¹ → A) ] P (g base))
  total = Σ-cong-equiv ((λ h → h ∘ deg₁ m) , localᵘ→preEquiv lA)
    (λ g → idEquiv (P (g base)))

separated-Σ-local : ∀ {ℓ ℓ' m} {A : Type ℓ} {P : A → Type ℓ'}
  → Separated m A → ((a : A) → Localᵘ m (P a))
  → Separated m (Σ A P)
separated-Σ-local {P = P} sepA lP (a , u) (b , v) =
  local-equiv (ΣPathTransport≃PathΣ (a , u) (b , v))
    (local-fiber (sepA a b) (lP b) (λ p → subst P p u) v)
