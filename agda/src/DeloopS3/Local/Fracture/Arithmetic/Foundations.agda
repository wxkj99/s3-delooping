{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.Foundations where

-- Connectedness, loop powers, and pullback squares.  No localization
-- preservation theorem or sequential-colimit theorem enters these proofs.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv ; totalEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Homotopy.Connected using (isConnected ; isConnectedPath)
import Cubical.HITs.Truncation as Tr
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Local.Base using (Local ; powLoop)
open import DeloopS3.Local.Powers using (powers→local)

Conn : Type → Type
Conn = isConnected 2

SC : Type → Type
SC = isConnected 3

connected-mere-path : (A : Type) → Conn A → (x y : A) → PT.∥ x ≡ y ∥₁
connected-mere-path A c x y = Tr.rec PT.squash₁ PT.∣_∣₁
  (fst (isConnectedPath 1 c x y))

connected-prop-elim : (A : Pointed ℓ-zero) → Conn (typ A)
  → (P : typ A → Type) → ((a : typ A) → isProp (P a))
  → P (pt A) → (a : typ A) → P a
connected-prop-elim A c P prop p a = PT.rec (prop a)
  (λ q → subst P q p) (connected-mere-path (typ A) c (pt A) a)

connected-Σ : (A : Type) (P : A → Type)
  → Conn A → ((a : A) → Conn (P a)) → Conn (Σ A P)
connected-Σ A P cA cP = center , Tr.elim
  (λ _ → isOfHLevelPath 2 (Tr.isOfHLevelTrunc 2) _ _)
  (λ { (a , p) → cong choose (snd cA Tr.∣ a ∣)
    ∙ cong (Tr.map (a ,_)) (snd (cP a) Tr.∣ p ∣) })
  where
  choose : Tr.hLevelTrunc 2 A → Tr.hLevelTrunc 2 (Σ A P)
  choose = Tr.rec (Tr.isOfHLevelTrunc 2)
    (λ a → Tr.map (a ,_) (fst (cP a)))
  center : Tr.hLevelTrunc 2 (Σ A P)
  center = choose (fst cA)

connected-fiber-SC-base : {E B : Type} (f : E → B)
  → Conn E → SC B → (b : B) → Conn (fiber f b)
connected-fiber-SC-base {E} {B} f cE cB b =
  connected-Σ E (λ e → f e ≡ b) cE (λ e → isConnectedPath 2 cB (f e) b)

connected-based-powers→local : (r : ℕ) (A : Pointed ℓ-zero)
  → Conn (typ A) → isEquiv (powLoop {X = typ A} {x = pt A} r)
  → Local r (typ A)
connected-based-powers→local r A c e = powers→local {X = typ A} {m = r}
  (connected-prop-elim A c
    (λ a → isEquiv (powLoop {X = typ A} {x = a} r))
    (λ a → isPropIsEquiv (powLoop {X = typ A} {x = a} r)) e)

PB : {A B C : Type} → (A → C) → (B → C) → Type
PB {A} {B} f g = Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ g b

module Square (A A' B B' : Type)
  (u : A → A') (f : A → B) (f' : A' → B') (v : B → B')
  (h : (a : A) → f' (u a) ≡ v (f a)) where

  gap : A → PB f' v
  gap a = u a , f a , h a

  Cartesian : Type
  Cartesian = isEquiv gap

  fiber-map : (b : B) → fiber f b → fiber f' (v b)
  fiber-map b (a , p) = u a , h a ∙ cong v p

  private
    P : B → Type
    P b = fiber f b
    Q : B → Type
    Q b = fiber f' (v b)

    domain : Iso (Σ B P) A
    Iso.fun domain (b , a , p) = a
    Iso.inv domain a = f a , a , refl
    Iso.sec domain a = refl
    Iso.ret domain (b , a , p) i = p i , a , λ j → p (i ∧ j)

    codomain : Iso (PB f' v) (Σ B Q)
    Iso.fun codomain (a , b , p) = b , a , p
    Iso.inv codomain (b , a , p) = a , b , p
    Iso.sec codomain _ = refl
    Iso.ret codomain _ = refl

    total : Σ B P → Σ B Q
    total (b , w) = b , fiber-map b w

    comparison : Iso.fun codomain ∘ gap ∘ Iso.fun domain ≡ total
    comparison = funExt λ { (b , a , p) →
      (λ i → p i , u a , compPath-filler (h a) (cong v p) i) }

  cartesian→fiberwise : Cartesian → (b : B) → isEquiv (fiber-map b)
  cartesian→fiberwise e = fiberEquiv P Q fiber-map
    (subst isEquiv comparison
      (snd (compEquiv (isoToEquiv domain)
        (compEquiv (gap , e) (isoToEquiv codomain)))))

  fiberwise→cartesian : ((b : B) → isEquiv (fiber-map b)) → Cartesian
  fiberwise→cartesian e = subst isEquiv agrees (snd composite)
    where
    composite : A ≃ PB f' v
    composite = compEquiv (isoToEquiv (invIso domain))
      (compEquiv (total , totalEquiv P Q fiber-map e)
        (isoToEquiv (invIso codomain)))
    agrees : fst composite ≡ gap
    agrees = funExt λ a → ΣPathP (refl , ΣPathP (refl , sym (rUnit (h a))))
