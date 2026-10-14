{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.Nat using (zero; suc; znots)
open import Cubical.Data.Fin using (toℕ-injective)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·; rUnitℤ·)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.SpanPi1.Character using (KleinNF; KleinCharacter; C₂; zero₂; one₂; module Generation)

-- Exactness suffices for normal forms; neither fibre injectivity nor an
-- order calculation is needed.
module CyclicExtension (K Q : Group₀) (f : GroupHom K Q) (r j : fst K)
  (kernel : (u : fst K) → fst f u ≡ GroupStr.1g (snd Q)
    → PT.∥ Σ[ a ∈ ℤ ] (a ℤ[ K ]· r) ≡ u ∥₁)
  (quotient : (v : fst Q) → PT.∥ Σ[ b ∈ ℤ ] v ≡ (b ℤ[ Q ]· fst f j) ∥₁)
  where
  private
    module K = GroupStr (snd K)
    module Q = GroupStr (snd Q)
  open GroupTheory K

  abstract
    generated : KleinNF K r j
    generated u = PT.rec PT.squash₁ step (quotient (fst f u)) where
      step : Σ[ b ∈ ℤ ] fst f u ≡ (b ℤ[ Q ]· fst f j)
        → PT.∥ Σ[ a ∈ ℤ ] Σ[ b ∈ ℤ ] u ≡ (a ℤ[ K ]· r) K.· (b ℤ[ K ]· j) ∥₁
      step (b , eq) = PT.map (λ { (a , p) → a , b ,
        sym (sym (K.·Assoc u (K.inv v) v)
          ∙ cong (u K.·_) (K.·InvL v) ∙ K.·IdR u)
        ∙ cong (K._· v) (sym p) }) (kernel (u K.· K.inv v) null)
        where
        v : fst K
        v = b ℤ[ K ]· j
        null : fst f (u K.· K.inv v) ≡ Q.1g
        null = IsGroupHom.pres· (snd f) u (K.inv v)
          ∙ cong₂ Q._·_ (eq ∙ sym (homPresℤ· f j b)) (IsGroupHom.presinv (snd f) v)
          ∙ Q.·InvR (fst f v)

module Image (K L : Group₀) (f : GroupHom K L)
  (onto : (v : fst L) → PT.∥ fiber (fst f) v ∥₁) where
  private
    module K = GroupStr (snd K)
    module L = GroupStr (snd L)

  abstract
    generated : (r j : fst K) → KleinNF K r j → KleinNF L (fst f r) (fst f j)
    generated r j nf v = PT.rec PT.squash₁ (λ { (u , p) →
      PT.map (λ { (a , b , h) → a , b , sym p ∙ cong (fst f) h
        ∙ Generation.hom-normal K L r j nf f a b }) (nf u) }) (onto v)

    inversion : (r j : fst K) → j K.· r ≡ K.inv r K.· j
      → fst f j L.· fst f r ≡ L.inv (fst f r) L.· fst f j
    inversion r j h = sym (IsGroupHom.pres· (snd f) j r)
      ∙ cong (fst f) h ∙ IsGroupHom.pres· (snd f) (K.inv r) j
      ∙ cong (L._· fst f j) (IsGroupHom.presinv (snd f) r)

abstract
  two-cases : (v : fst C₂) → (v ≡ zero₂ → ⊥) → v ≡ one₂
  two-cases (zero , p) nz = Empty.rec (nz (toℕ-injective {k = 2} refl))
  two-cases (suc zero , p) nz = toℕ-injective {k = 2} refl
  two-cases (suc (suc n) , ()) nz

  -- Surjectivity forces the second generator to be odd, without ever
  -- computing its signed projection around RP¹.
  character : (K : Group₀) (χ : GroupHom K C₂) (r j : fst K)
    → GroupStr._·_ (snd K) j r ≡ GroupStr._·_ (snd K) (GroupStr.inv (snd K) r) j
    → KleinNF K r j → fst χ r ≡ zero₂
    → ((v : fst C₂) → PT.∥ fiber (fst χ) v ∥₁)
    → KleinCharacter K χ
  character K χ r j inversion generated r-zero onto = record
    { r = r ; j = j ; inversion = inversion ; generated = generated
    ; r-zero = r-zero ; j-one = two-cases (fst χ j) nonzero }
    where
    module C = GroupStr (snd C₂)
    trivial : fst χ j ≡ zero₂ → (u : fst K) → fst χ u ≡ zero₂
    trivial pj u = PT.rec (C.is-set _ _) (λ { (a , b , p) →
      cong (fst χ) p ∙ Generation.hom-normal K C₂ r j generated χ a b
      ∙ cong₂ C._·_ (cong (λ x → a ℤ[ C₂ ]· x) r-zero ∙ rUnitℤ· C₂ a)
        (cong (λ x → b ℤ[ C₂ ]· x) pj ∙ rUnitℤ· C₂ b)
      ∙ C.·IdL zero₂ }) (generated u)
    nonzero : fst χ j ≡ zero₂ → ⊥
    nonzero pj = PT.rec Empty.isProp⊥
      (λ { (u , p) → znots (cong fst (sym (trivial pj u) ∙ p)) }) (onto one₂)
