{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CharacterAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·)
import Cubical.HITs.PropositionalTruncation as PT

KleinNF : (K : Group₀) → fst K → fst K → Type₀
KleinNF K r j = (u : fst K) → PT.∥ Σ[ a ∈ ℤ ] Σ[ b ∈ ℤ ]
  u ≡ GroupStr._·_ (snd K) (a ℤ[ K ]· r) (b ℤ[ K ]· j) ∥₁

NonabelianImage : {K H : Group₀} → GroupHom K H → Type₀
NonabelianImage {K} {H} f = PT.∥ Σ[ u ∈ fst K ] Σ[ v ∈ fst K ]
  ((GroupStr._·_ (snd H) (fst f u) (fst f v)
    ≡ GroupStr._·_ (snd H) (fst f v) (fst f u)) → ⊥) ∥₁

module Commutation (G : Group₀) where
  open GroupStr (snd G)
  open GroupTheory G

  Comm : fst G → fst G → Type₀
  Comm x y = x · y ≡ y · x

  abstract
    mul-right : (x y z : fst G) → Comm x y → Comm x z → Comm x (y · z)
    mul-right x y z p q = ·Assoc x y z ∙ cong (_· z) p
      ∙ sym (·Assoc y x z) ∙ cong (y ·_) q ∙ ·Assoc y z x

    mul-left : (x y z : fst G) → Comm x z → Comm y z → Comm (x · y) z
    mul-left x y z p q = sym (mul-right z x y (sym p) (sym q))

    inv-right : (x y : fst G) → Comm x y → Comm x (inv y)
    inv-right x y p = ·CancelR y
      (sym (·Assoc x (inv y) y) ∙ cong (x ·_) (·InvL y) ∙ ·IdR x
       ∙ sym (sym (·Assoc (inv y) x y) ∙ cong (inv y ·_) p
         ∙ ·Assoc (inv y) y x ∙ cong (_· x) (·InvL y) ∙ ·IdL x))

    power-right : (x y : fst G) → Comm x y → (n : ℤ) → Comm x (n ℤ[ G ]· y)
    power-right x y p (pos zero) = ·IdR x ∙ sym (·IdL x)
    power-right x y p (pos (suc n)) = mul-right x y (pos n ℤ[ G ]· y) p (power-right x y p (pos n))
    power-right x y p (negsuc zero) = inv-right x y p
    power-right x y p (negsuc (suc n)) = mul-right x (inv y) (negsuc n ℤ[ G ]· y)
      (inv-right x y p) (power-right x y p (negsuc n))

    powers : (x y : fst G) → Comm x y → (a b : ℤ)
      → Comm (a ℤ[ G ]· x) (b ℤ[ G ]· y)
    powers x y p a b = power-right (a ℤ[ G ]· x) y
      (sym (power-right y x (sym p) a)) b

    normal-forms : (r j : fst G) → Comm r j → (a b c d : ℤ)
      → Comm ((a ℤ[ G ]· r) · (b ℤ[ G ]· j)) ((c ℤ[ G ]· r) · (d ℤ[ G ]· j))
    normal-forms r j p a b c d = mul-right _ _ _
      (mul-left _ _ _ (powers r r refl a c) (powers j r (sym p) b c))
      (mul-left _ _ _ (powers r j p a d) (powers j j refl b d))

    square-inversion-commute : (a b : fst G)
      → b · a ≡ inv a · b → a · a ≡ 1g → Comm a b
    square-inversion-commute a b rel sq =
      sym (rel ∙ cong (_· b) (sym (invUniqueR sq)))

module Generation (K H : Group₀) (r j : fst K) (nf : KleinNF K r j) where
  private
    module K = GroupStr (snd K)
    module H = GroupStr (snd H)
  open Commutation H

  abstract
    hom-normal : (f : GroupHom K H) (a b : ℤ)
      → fst f ((a ℤ[ K ]· r) K.· (b ℤ[ K ]· j))
        ≡ (a ℤ[ H ]· fst f r) H.· (b ℤ[ H ]· fst f j)
    hom-normal f a b = IsGroupHom.pres· (snd f) _ _
      ∙ cong₂ H._·_ (homPresℤ· f r a) (homPresℤ· f j b)

    agree : (f g : GroupHom K H) → fst f r ≡ fst g r → fst f j ≡ fst g j
      → (u : fst K) → fst f u ≡ fst g u
    agree f g pr pj u = PT.rec (H.is-set _ _) (λ { (a , b , p) →
      cong (fst f) p ∙ hom-normal f a b
      ∙ cong₂ H._·_ (cong (λ x → a ℤ[ H ]· x) pr) (cong (λ x → b ℤ[ H ]· x) pj)
      ∙ sym (hom-normal g a b) ∙ sym (cong (fst g) p) }) (nf u)

    commuting-image : (f : GroupHom K H) → Comm (fst f r) (fst f j)
      → (u v : fst K) → Comm (fst f u) (fst f v)
    commuting-image f p u v = PT.rec (H.is-set _ _) (λ { (a , b , pu) →
      PT.rec (H.is-set _ _) (λ { (c , d , pv) →
        cong₂ H._·_ (cong (fst f) pu ∙ hom-normal f a b) (cong (fst f) pv ∙ hom-normal f c d)
        ∙ normal-forms (fst f r) (fst f j) p a b c d
        ∙ sym (cong₂ H._·_ (cong (fst f) pv ∙ hom-normal f c d) (cong (fst f) pu ∙ hom-normal f a b)) }) (nf v) }) (nf u)

    noncommuting-generators : (f : GroupHom K H) → NonabelianImage f
      → Comm (fst f r) (fst f j) → ⊥
    noncommuting-generators f nonab p = PT.rec isProp⊥
      (λ { (u , v , neq) → neq (commuting-image f p u v) }) nonab
