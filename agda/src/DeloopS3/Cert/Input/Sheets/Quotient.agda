{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets.Quotient where

-- Descend the normal-form sheet coordinate to H\G.
-- This is independent of the finite enumeration or the index numbers.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase)
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Cover.Cosets

module FromNormalForm (H G : Group₀) (j : SubgroupEmbedding H G)
  (S : Type₀) (setS : isSet S) (rep : S → G .fst)
  (nf : (H .fst × S) ≃ G .fst)
  (nf-pack : (x : H .fst × S)
    → equivFun nf x ≡ GroupStr._·_ (G .snd) (hom j .fst (x .fst)) (rep (x .snd))) where
  private
    module HG = GroupStr (H .snd)
    module GG = GroupStr (G .snd)
    module JH = IsGroupHom (hom j .snd)
    module Q = RightCosets j

  pack : H .fst × S → G .fst
  pack (h , i) = hom j .fst h GG.· rep i

  indexOf : G .fst → S
  indexOf g = invEq nf g .snd

  abstract
    factor : (g : G .fst) → pack (invEq nf g) ≡ g
    factor g = sym (nf-pack (invEq nf g)) ∙ secEq nf g

    index-pack : (x : H .fst × S) → indexOf (pack x) ≡ x .snd
    index-pack x = cong indexOf (sym (nf-pack x)) ∙ cong snd (retEq nf x)

    left-factor : (h : H .fst) (g : G .fst)
      → pack (h HG.· invEq nf g .fst , indexOf g) ≡ hom j .fst h GG.· g
    left-factor h g = cong (GG._· rep (indexOf g)) (JH.pres· h (invEq nf g .fst))
      ∙ sym (GG.·Assoc (hom j .fst h) (hom j .fst (invEq nf g .fst)) (rep (indexOf g)))
      ∙ cong (hom j .fst h GG.·_) (factor g)

    index-left : (h : H .fst) (g : G .fst) → indexOf (hom j .fst h GG.· g) ≡ indexOf g
    index-left h g = cong indexOf (sym (left-factor h g))
      ∙ index-pack (h HG.· invEq nf g .fst , indexOf g)

    index-respects : (g g′ : G .fst) → Q.Rel g g′ → indexOf g ≡ indexOf g′
    index-respects g g′ (h , eq) = cong indexOf (sym eq) ∙ index-left h g′

    index-rep : (i : S) → indexOf (rep i) ≡ i
    index-rep i = cong indexOf (sym (cong (GG._· rep i) JH.pres1 ∙ GG.·IdL (rep i)))
      ∙ index-pack (HG.1g , i)

  fromCoset : Q.Cosets → S
  fromCoset = SQ.rec setS indexOf index-respects

  toCoset : S → Q.Cosets
  toCoset i = SQ.[ rep i ]

  abstract
    coset-sec : (x : Q.Cosets) → toCoset (fromCoset x) ≡ x
    coset-sec = SQ.elimProp (λ x → SQ.squash/ _ _)
      (λ g → sym (SQ.eq/ g (rep (indexOf g)) (invEq nf g .fst , factor g)))

  sheets≃cosets : S ≃ Q.Cosets
  sheets≃cosets = isoToEquiv (iso toCoset fromCoset coset-sec index-rep)

  sheets≃fiber : S ≃ CosetFamily j embase .fst
  sheets≃fiber = compEquiv sheets≃cosets Q.cosets≃fiber

  sheets-at-rep : (i : S) → equivFun sheets≃fiber i ≡ cosetPoint j (rep i)
  sheets-at-rep i = refl
