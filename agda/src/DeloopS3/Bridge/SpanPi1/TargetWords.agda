{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetWords where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_)
import Cubical.HITs.PropositionalTruncation as PT

-- Ordinary finite group words, including inverses.  The witness is only
-- ever eliminated from propositional truncation into a proposition.
data Word : Type₀ where
  unit X Y : Word
  mul : Word → Word → Word
  inverse : Word → Word

module Membership {ℓ} (G : Group ℓ) (x y : fst G) where
  open GroupStr (snd G)
  open GroupTheory G

  eval : Word → fst G
  eval unit = 1g
  eval X = x
  eval Y = y
  eval (mul v w) = eval v · eval w
  eval (inverse v) = inv (eval v)

  Generated : fst G → Type ℓ
  Generated u = PT.∥ Σ[ v ∈ Word ] eval v ≡ u ∥₁

  one : Generated 1g
  one = PT.∣ unit , refl ∣₁
  gen-x : Generated x
  gen-x = PT.∣ X , refl ∣₁
  gen-y : Generated y
  gen-y = PT.∣ Y , refl ∣₁

  product : {u v : fst G} → Generated u → Generated v → Generated (u · v)
  product = PT.rec (isPropΠ (λ _ → PT.squash₁)) (λ { (a , p) → PT.rec PT.squash₁
    (λ { (b , q) → PT.∣ mul a b , cong₂ _·_ p q ∣₁ }) })

  invert : {u : fst G} → Generated u → Generated (inv u)
  invert = PT.map (λ { (a , p) → inverse a , cong inv p })

  power : (n : ℤ) {u : fst G} → Generated u → Generated (n ℤ[ G ]· u)
  power (pos zero) p = one
  power (pos (suc n)) p = product p (power (pos n) p)
  power (negsuc zero) p = invert p
  power (negsuc (suc n)) p = product (invert p) (power (negsuc n) p)

  abstract
    kill : (L : Group ℓ) (f : GroupHom G L)
      → fst f x ≡ GroupStr.1g (snd L)
      → fst f y ≡ GroupStr.1g (snd L)
      → (u : fst G) → Generated u → fst f u ≡ GroupStr.1g (snd L)
    kill L f px py u = PT.rec (GroupStr.is-set (snd L) _ _)
      (λ { (a , p) → cong (fst f) (sym p) ∙ on-word a })
      where
      module L = GroupStr (snd L)
      on-word : (a : Word) → fst f (eval a) ≡ L.1g
      on-word unit = IsGroupHom.pres1 (snd f)
      on-word X = px
      on-word Y = py
      on-word (mul a b) = IsGroupHom.pres· (snd f) _ _
        ∙ cong₂ L._·_ (on-word a) (on-word b) ∙ L.·IdL L.1g
      on-word (inverse a) = IsGroupHom.presinv (snd f) _
        ∙ cong L.inv (on-word a) ∙ GroupTheory.inv1g L

abstract
  map-eval : (G L : Group₀) (x y : fst G) (f : GroupHom G L) (v : Word)
    → fst f (Membership.eval G x y v)
      ≡ Membership.eval L (fst f x) (fst f y) v
  map-eval G L x y f unit = IsGroupHom.pres1 (snd f)
  map-eval G L x y f X = refl
  map-eval G L x y f Y = refl
  map-eval G L x y f (mul v w) = IsGroupHom.pres· (snd f) _ _
    ∙ cong₂ (GroupStr._·_ (snd L)) (map-eval G L x y f v) (map-eval G L x y f w)
  map-eval G L x y f (inverse v) = IsGroupHom.presinv (snd f) _
    ∙ cong (GroupStr.inv (snd L)) (map-eval G L x y f v)
