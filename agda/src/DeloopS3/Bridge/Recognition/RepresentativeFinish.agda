{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.RepresentativeFinish where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)
open import Cubical.Homotopy.Group.Base using (π'Gr)
open import Cubical.Homotopy.Connected using (isConnected ; isConnectedSubtr')
open import Cubical.HITs.Sn.Base using (S₊∙)
open import Cubical.HITs.Pushout.Base using (inr)
open import Cubical.CW.HurewiczTheorem using
  (HurewiczMap ; HurewiczMapUntrunc ; HurewiczHom)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.Recognition.HurewiczBase using (hurewicz-isEquiv)
open import DeloopS3.Bridge.Recognition.Extension using (Moore)
open import DeloopS3.Bridge.Recognition.Torsion using
  (multiple ; reflect-multiple-zero ; extend-moore3-from-torsion)

-- Algebra first: replace the value of an abstract homomorphism by a
-- specified representative, then reflect torsion through its equivalence.
-- Neither the group laws nor the homomorphism proof are unfolded here.
private
  abstract
    reflect-at : (G H : Group ℓ-zero) (f : fst G → fst H)
      (hom : IsGroupHom (snd G) f (snd H)) (equiv : isEquiv f)
      (m : ℕ) (z : fst G) (h : fst H) → f z ≡ h
      → multiple H m h ≡ GroupStr.1g (snd H)
      → multiple G m z ≡ GroupStr.1g (snd G)
    reflect-at G H f hom equiv m z h value torsion =
      reflect-multiple-zero {G = G} {H = H} (f , hom) equiv m z
        (cong (multiple H m) value ∙ torsion)

  -- Only this small map is unfolded when proving its three interfaces.
  opaque
    hurewicz3 : (X : CW₀) (x : fst X)
      → fst (π'Gr 2 (fst X , x)) → fst (H̃ᶜʷ X 3)
    hurewicz3 X x = HurewiczMap {ℓ = ℓ-zero} {n = 2} X x

  opaque
    unfolding hurewicz3

    hurewicz3-hom : (X : CW₀) (x : fst X)
      (conn : isConnected 4 (fst X))
      → IsGroupHom (snd (π'Gr 2 (fst X , x))) (hurewicz3 X x)
          (snd (H̃ᶜʷ X 3))
    hurewicz3-hom X x conn = snd
      (HurewiczHom {ℓ = ℓ-zero} {n = 2} X x
        (isConnectedSubtr' {A = fst X} 2 2 conn))

    hurewicz3-equiv : (X : CW₀) (x : fst X)
      (conn : isConnected 4 (fst X)) → isEquiv (hurewicz3 X x)
    hurewicz3-equiv X x conn = hurewicz-isEquiv X 1 conn x

    hurewicz3-value : (X : CW₀) (x : fst X)
      (s : S₊∙ 3 →∙ (fst X , x))
      → hurewicz3 X x ST.∣ s ∣₂ ≡ HurewiczMapUntrunc {n = 2} X x s
    hurewicz3-value X x s = refl

-- If m times the Hurewicz class vanishes, equivalence and the homomorphism
-- law give m[s] = 0.  The torsion extension theorem then supplies
-- the Moore extension, without choosing a nullhomotopy outside truncation.
abstract
  extend-moore3-from-homology-torsion : (m : ℕ) (X : CW₀)
    (conn : isConnected 4 (fst X)) (x : fst X)
    (s : S₊∙ 3 →∙ (fst X , x))
    → multiple (H̃ᶜʷ X 3) m (HurewiczMapUntrunc {n = 2} X x s)
      ≡ GroupStr.1g (snd (H̃ᶜʷ X 3))
    → PT.∥ Σ[ f ∈ (Moore m 2 → fst X) ] (f ∘ inr ≡ fst s) ∥₁
  extend-moore3-from-homology-torsion m X conn x s torsion =
    extend-moore3-from-torsion m {X = fst X , x} s
      (reflect-at (π'Gr 2 (fst X , x)) (H̃ᶜʷ X 3)
        (hurewicz3 X x) (hurewicz3-hom X x conn) (hurewicz3-equiv X x conn)
        m ST.∣ s ∣₂ (HurewiczMapUntrunc {ℓ = ℓ-zero} {n = 2} X x s)
        (hurewicz3-value X x s) torsion)

