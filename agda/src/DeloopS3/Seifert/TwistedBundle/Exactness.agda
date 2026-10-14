{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- LES criteria for π₂ vanishing from an injective connecting homomorphism,
-- with integer-coordinate and nonzero fibre-relation specializations.
module DeloopS3.Seifert.TwistedBundle.Exactness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Int using (ℤ; pos; _·_; ·lCancel; ·≢0; abs)
open import Cubical.Data.Nat using (snotz)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (compGroupHom; GroupEquiv→GroupHom; invGroupEquiv)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction using (characGroupHomℤ)
open import Cubical.Homotopy.Group.Base using (π; πGr; 1π)
open import Cubical.Homotopy.Group.LES using (module πLES)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetTruncation as ST

pi₂-groupoid-zero : ∀ {ℓ} {X : Type ℓ} → isGroupoid X
  → (x : X) → isContr (π 2 (X , x))
pi₂-groupoid-zero gx x = 1π 2 , ST.elim
  (λ _ → isProp→isSet (ST.squash₂ _ _))
  (λ p → cong ST.∣_∣₂ (gx x x refl refl refl p))

-- A homomorphism Z → Z with any nonzero image is injective; its value at
-- the chosen witness suffices without computing a generator coordinate.
integer-hom-nonzero-injective : (h : GroupHom ℤGroup ℤGroup) (n : ℤ)
  → ¬ h .fst n ≡ pos 0
  → (x y : ℤ) → h .fst x ≡ h .fst y → x ≡ y
integer-hom-nonzero-injective h n nz x y p =
  ·lCancel (h .fst (pos 1)) x y
    (sym (coordinate x) ∙ p ∙ coordinate y) coefficient-nonzero
  where
  coordinate : (x : ℤ) → h .fst x ≡ h .fst (pos 1) · x
  coordinate x = cong (λ f → f .fst x) (characGroupHomℤ h)
  coefficient-nonzero : ¬ h .fst (pos 1) ≡ pos 0
  coefficient-nonzero q = nz (coordinate n ∙ cong (_· n) q)

module Sequence {ℓM ℓB : Level} {M : Pointed ℓM} {Base : Pointed ℓB}
  (p : M →∙ Base) where
  module LES = πLES p

  connecting : GroupHom (πGr 1 Base) (πGr 0 LES.fib)
  connecting = LES.B→fib 0

  -- This is exactness at π₂(M) and π₂(Base), not an assumed LES field.
  vanishing-from-injective-boundary : isContr (π 2 LES.fib)
    → ((x y : π 2 Base) → connecting .fst x ≡ connecting .fst y → x ≡ y)
    → isContr (π 2 M)
  vanishing-from-injective-boundary fibre-zero injective = 1π 2 , contract
    where
    p₂ : GroupHom (πGr 1 M) (πGr 1 Base)
    p₂ = LES.A→B 1

    p₂-zero : (x : π 2 M) → p₂ .fst x ≡ 1π 2
    p₂-zero x = injective (p₂ .fst x) (1π 2)
      (LES.Im-A→B⊂Ker-B→fib 0 (p₂ .fst x) PT.∣ x , refl ∣₁
       ∙ sym (IsGroupHom.pres1 (connecting .snd)))

    contract : (x : π 2 M) → 1π 2 ≡ x
    contract x = PT.rec (ST.squash₂ _ _)
      (λ { (y , h) → sym (IsGroupHom.pres1 (LES.fib→A 1 .snd))
         ∙ cong (LES.fib→A 1 .fst)
             (isContr→isProp fibre-zero (1π 2) y) ∙ h })
      (LES.Ker-A→B⊂Im-fib→A 1 x (p₂-zero x))

  -- The coordinate calculation is an explicit hypothesis of this criterion,
  -- not a consequence of finite π₁.
  boundary-injective-from-integer-coordinate : (d : ℤ) → ¬ d ≡ pos 0
    → (baseChart : π 2 Base ≃ ℤ) → (fibreChart : π 1 LES.fib ≃ ℤ)
    → ((x : π 2 Base) → fibreChart .fst (connecting .fst x)
      ≡ d · baseChart .fst x)
    → (x y : π 2 Base) → connecting .fst x ≡ connecting .fst y → x ≡ y
  boundary-injective-from-integer-coordinate d nonzero b f compute x y h =
    invEq (congEquiv b) (·lCancel d (b .fst x) (b .fst y)
      (sym (compute x) ∙ cong (f .fst) h ∙ compute y) nonzero)

  vanishing-from-integer-coordinate : isContr (π 2 LES.fib)
    → (d : ℤ) → ¬ d ≡ pos 0
    → (baseChart : π 2 Base ≃ ℤ) → (fibreChart : π 1 LES.fib ≃ ℤ)
    → ((x : π 2 Base) → fibreChart .fst (connecting .fst x)
      ≡ d · baseChart .fst x)
    → isContr (π 2 M)
  vanishing-from-integer-coordinate h d nz b f compute =
    vanishing-from-injective-boundary h
      (boundary-injective-from-integer-coordinate d nz b f compute)

  -- The fibre-relation criterion requires a kernel element of the actual
  -- fibre inclusion, not merely a relation in an abstract presented group.
  -- Exactness supplies a nonzero image of the boundary. No Euler sign or
  -- exact order of the fibre generator is needed for this criterion.
  vanishing-from-fibre-relation : isContr (π 2 LES.fib)
    → (b : GroupEquiv (πGr 1 Base) ℤGroup)
    → (f : GroupEquiv (πGr 0 LES.fib) ℤGroup)
    → (y : π 1 LES.fib) → ¬ f .fst .fst y ≡ pos 0
    → isInKer (LES.fib→A 0) y
    → isContr (π 2 M)
  vanishing-from-fibre-relation fibre-zero b f y nz relation =
    PT.rec isPropIsContr
      (λ { (x , hx) → vanishing-from-injective-boundary fibre-zero (injective x hx) })
      (LES.Ker-fib→A⊂Im-B→fib 0 y relation)
    where
    h : GroupHom ℤGroup ℤGroup
    h = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv b))
      (compGroupHom connecting (GroupEquiv→GroupHom f))

    coordinate : (x : π 2 Base)
      → h .fst (b .fst .fst x) ≡ f .fst .fst (connecting .fst x)
    coordinate x = cong (λ u → f .fst .fst (connecting .fst u)) (retEq (b .fst) x)

    image-nonzero : (x : π 2 Base) → connecting .fst x ≡ y
      → ¬ h .fst (b .fst .fst x) ≡ pos 0
    image-nonzero x hx q = nz
      (sym (cong (f .fst .fst) hx) ∙ sym (coordinate x) ∙ q)

    injective : (x : π 2 Base) → connecting .fst x ≡ y
      → (u v : π 2 Base) → connecting .fst u ≡ connecting .fst v → u ≡ v
    injective x hx u v p = invEq (congEquiv (b .fst))
      (integer-hom-nonzero-injective h (b .fst .fst x) (image-nonzero x hx)
        (b .fst .fst u) (b .fst .fst v)
        (coordinate u ∙ cong (f .fst .fst) p ∙ sym (coordinate v)))

-- Both ±2e conventions are covered by using an arbitrary nonzero d above.
twice-nonzero : (e : ℤ) → ¬ e ≡ pos 0 → ¬ (pos 2 · e) ≡ pos 0
twice-nonzero e nz = ·≢0 {x = pos 2} {y = e} (λ h → snotz (cong abs h)) nz
