{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.Torsion where

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

multiple : (G : Group ℓ-zero) → ℕ → fst G → fst G
multiple G zero z = GroupStr.1g (snd G)
multiple G (suc m) z = GroupStr._·_ (snd G) z (multiple G m z)

abstract
  pres-multiple : {G H : Group ℓ-zero} (f : GroupHom G H) (m : ℕ) (z : fst G)
    → fst f (multiple G m z) ≡ multiple H m (fst f z)
  pres-multiple f zero z = IsGroupHom.pres1 (snd f)
  pres-multiple {H = H} f (suc m) z = IsGroupHom.pres· (snd f) z _
    ∙ cong (GroupStr._·_ (snd H) (fst f z)) (pres-multiple f m z)

  reflect-multiple-zero : {G H : Group ℓ-zero} (f : GroupHom G H)
    → isEquiv (fst f) → (m : ℕ) (z : fst G)
    → multiple H m (fst f z) ≡ GroupStr.1g (snd H)
    → multiple G m z ≡ GroupStr.1g (snd G)
  reflect-multiple-zero {G} {H} f ef m z torsion =
    sym (retEq e (multiple G m z))
    ∙ cong (invEq e) (pres-multiple f m z ∙ torsion ∙ sym (IsGroupHom.pres1 (snd f)))
    ∙ retEq e (GroupStr.1g (snd G))
    where
    e : fst G ≃ fst H
    e = fst f , ef

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

  degree3-class : (m : ℕ)
    → ST.∣ (degSphere m 2 , refl) ∣₂ ≡ ST.∣ sphere-multiple 2 m ∣₂
  degree3-class m = same-degree→same-class 2 (degSphere m 2 , refl) (sphere-multiple 2 m)
    (degree-degSphere-S³ m ∙ sym (degree-sphere-multiple 2 m))

precompose-degree3-class : (m : ℕ) {X : Pointed ℓ-zero} (s : S₊∙ 3 →∙ X)
  → ST.∣ s ∘∙ (degSphere m 2 , refl) ∣₂
    ≡ multiple (π'Gr 2 X) m ST.∣ s ∣₂
precompose-degree3-class m {X} s =
  cong (fst (π'∘∙Hom 2 s)) (degree3-class m ∙ sphere-multiple-class 2 m)
  ∙ pres-multiple (π'∘∙Hom 2 s) m ST.∣ idfun∙ (S₊∙ 3) ∣₂
  ∙ cong (multiple (π'Gr 2 X) m) (cong ST.∣_∣₂ (∘∙-idˡ s))

extend-moore3-from-torsion : (m : ℕ) {X : Pointed ℓ-zero} (s : S₊∙ 3 →∙ X)
  → multiple (π'Gr 2 X) m ST.∣ s ∣₂ ≡ GroupStr.1g (snd (π'Gr 2 X))
  → PT.∥ Σ[ f ∈ (Moore m 2 → fst X) ] (f ∘ inr ≡ fst s) ∥₁
extend-moore3-from-torsion m {X} s torsion = extend-moore m 2 (fst s) (snd X)
  (PT.map (cong fst) (Iso.fun ST.PathIdTrunc₀Iso
    (precompose-degree3-class m s ∙ torsion)))
