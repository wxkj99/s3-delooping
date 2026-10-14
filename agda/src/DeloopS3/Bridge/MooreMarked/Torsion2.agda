{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.MooreMarked.Torsion2 where

-- Degree-m precomposition acts by multiplication by m on sphere
-- homotopy classes.
open import DeloopS3.Bridge.Recognition.Extension
open import DeloopS3.Bridge.Recognition.Degree
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (pos ; pos+) renaming (_+_ to _+ℤ_)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.HITs.Sn.Base using (S₊∙ ; ptSn)
open import Cubical.HITs.Sn.Degree using (degree ; degreeConst ; degreeIdfun ; degreeHom ; degree∥₂Iso)
open import Cubical.HITs.Pushout.Base using (inr)
open import Cubical.Homotopy.Group.Base using (π'Gr ; π'∘∙Hom ; 1Π ; ∙Π)
open import Cubical.Homotopy.Group.PinSn using (πₙSⁿ-unpointIso)
open import DeloopS3.Local.Powers using (degSphere)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Bridge.Recognition.Torsion using (multiple ; pres-multiple)
open import DeloopS3.Local.EI using (BottomMoore)

private
  sphere-multiple : (n m : ℕ) → S₊∙ (suc n) →∙ S₊∙ (suc n)
  sphere-multiple n zero = 1Π
  sphere-multiple n (suc m) = ∙Π (idfun∙ (S₊∙ (suc n))) (sphere-multiple n m)

  sphere-multiple-class : (n m : ℕ)
    → ST.∣ sphere-multiple n m ∣₂
      ≡ multiple (π'Gr n (S₊∙ (suc n))) m ST.∣ idfun∙ (S₊∙ (suc n)) ∣₂
  sphere-multiple-class n zero = refl
  sphere-multiple-class n (suc m) =
    cong (GroupStr._·_ (snd (π'Gr n (S₊∙ (suc n)))) ST.∣ idfun∙ (S₊∙ (suc n)) ∣₂)
      (sphere-multiple-class n m)

  degree-sphere-multiple : (n m : ℕ)
    → degree (suc n) (fst (sphere-multiple n m)) ≡ pos m
  degree-sphere-multiple n zero = degreeConst (suc n)
  degree-sphere-multiple n (suc m) =
    degreeHom {n = n} (idfun∙ (S₊∙ (suc n))) (sphere-multiple n m)
    ∙ cong₂ _+ℤ_ (degreeIdfun (suc n)) (degree-sphere-multiple n m)
    ∙ sym (pos+ 1 m)

  same-degree→same-class : (n : ℕ) (f g : S₊∙ (suc n) →∙ S₊∙ (suc n))
    → degree (suc n) (fst f) ≡ degree (suc n) (fst g)
    → ST.∣ f ∣₂ ≡ ST.∣ g ∣₂
  same-degree→same-class n f g p =
    sym (Iso.ret e ST.∣ f ∣₂) ∙ cong (Iso.inv e) p ∙ Iso.ret e ST.∣ g ∣₂
    where
    e = compIso (πₙSⁿ-unpointIso n) (degree∥₂Iso n)

  degree2-class : (m : ℕ)
    → ST.∣ (degSphere m 1 , refl) ∣₂ ≡ ST.∣ sphere-multiple 1 m ∣₂
  degree2-class m = same-degree→same-class 1 (degSphere m 1 , refl) (sphere-multiple 1 m)
    (degree-degSphere-S² m ∙ sym (degree-sphere-multiple 1 m))

precompose-degree2-class : (m : ℕ) {X : Pointed ℓ-zero} (s : S₊∙ 2 →∙ X)
  → ST.∣ s ∘∙ (degSphere m 1 , refl) ∣₂
    ≡ multiple (π'Gr 1 X) m ST.∣ s ∣₂
precompose-degree2-class m {X} s =
  cong (fst (π'∘∙Hom 1 s)) (degree2-class m ∙ sphere-multiple-class 1 m)
  ∙ pres-multiple (π'∘∙Hom 1 s) m ST.∣ idfun∙ (S₊∙ 2) ∣₂
  ∙ cong (multiple (π'Gr 1 X) m) (cong ST.∣_∣₂ (∘∙-idˡ s))

extend-moore2-from-torsion : (m : ℕ) {X : Pointed ℓ-zero} (s : S₊∙ 2 →∙ X)
  → multiple (π'Gr 1 X) m ST.∣ s ∣₂ ≡ GroupStr.1g (snd (π'Gr 1 X))
  → PT.∥ Σ[ f ∈ (Moore m 1 → fst X) ] (f ∘ inr ≡ fst s) ∥₁
extend-moore2-from-torsion m {X} s torsion = extend-moore m 1 (fst s) (snd X)
  (PT.map (cong fst) (Iso.fun ST.PathIdTrunc₀Iso
    (precompose-degree2-class m s ∙ torsion)))
