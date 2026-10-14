{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom; GroupEquiv→GroupHom)
open import Cubical.Homotopy.Group.Base using (πHom)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.KleinBottle.Base as KB
import Cubical.HITs.KleinBottle.Properties as KP
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)
open import DeloopS3.Bridge.SpanPi1.Character using (KleinCharacter; C₂)
open import DeloopS3.Bridge.SpanPi1.Connected using (circle-paths)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill)
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus as M
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops as Loops
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Klein as Klein
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Filled as Filled
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Cap as Cap

At : (X : Type₀) → (X → RP²) → X → Type₀
At X q a = (rp : GroupEquiv (Π RP² (q a)) C₂)
  → PT.∥ KleinCharacter (Π X a)
      (compGroupHom (πHom 0 (q , refl)) (GroupEquiv→GroupHom rp)) ∥₁

Everywhere : (X : Type₀) → (X → RP²) → Type₀
Everywhere X q = (a : X) → At X q a

abstract
  change-point : (X : Type₀) (q : X → RP²) (a : X)
    → ((x : X) → PT.∥ a ≡ x ∥₁) → At X q a → Everywhere X q
  change-point X q a paths at x = PT.rec (isPropΠ (λ _ → PT.squash₁))
    (λ p → subst (At X q) p at) (paths x)

  -- Equivalence induction transports the ENTIRE package, including the
  -- literal map q and its pointing. There is no named target-loop action.
  pullback : {X Y : Type₀} (e : X ≃ Y) (q : Y → RP²)
    → Everywhere Y q → Everywhere X (q ∘ fst e)
  pullback {Y = Y} e = EquivJ
    (λ X e → (q : Y → RP²) → Everywhere Y q → Everywhere X (q ∘ fst e))
    (λ q p → p) e

  klein-paths : (x : M.Kinv) → PT.∥ Klein.point ≡ x ∥₁
  klein-paths x = PT.map (λ p → sym M.klein-base
    ∙ cong (fst M.klein≃Kinv) p ∙ secEq M.klein≃Kinv x)
    (KP.elimProp {A = λ z → PT.∥ KB.point ≡ z ∥₁}
      (λ _ → PT.squash₁) PT.∣ refl ∣₁ (invEq M.klein≃Kinv x))

module AllFilled (e : ℤ) where
  module F = Filled.Filled e
  module G = Cap.Geometry e
  module L = Loops.Filling e

  abstract
    paths : (x : Fill e) → PT.∥ F.point ≡ x ∥₁
    paths (inl x) = PT.map (cong L.include) (klein-paths x)
    paths (inr t) = PT.map
      (λ p → cong L.include (sym M.klein-base) ∙ L.seam ∙ cong L.core p)
      (circle-paths t)
    paths (push z i) = isProp→PathP
      {B = λ k → PT.∥ F.point ≡ push z k ∥₁}
      (λ _ → PT.squash₁) (paths (inl _)) (paths (inr _)) i

    everywhere : Everywhere (Fill e) G.projection
    everywhere = change-point (Fill e) G.projection F.point paths
      (λ rp → PT.∣ F.character rp ∣₁)

    bundle-map : G.projection ∘ invEq G.equivalence ≡ Bundle.pₑ e
    bundle-map = funExt (λ m → funExt⁻ G.projection-map (invEq G.equivalence m)
      ∙ cong (Bundle.pₑ e) (secEq G.equivalence m))

    bundle-character : Everywhere (Bundle.Mₑ e) (Bundle.pₑ e)
    bundle-character = subst (Everywhere (Bundle.Mₑ e)) bundle-map
      (pullback (invEquiv G.equivalence) G.projection everywhere)
