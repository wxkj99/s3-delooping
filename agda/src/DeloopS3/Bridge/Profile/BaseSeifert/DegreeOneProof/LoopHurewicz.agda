{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopHurewicz where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.SetTruncation using (∣_∣₂)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Group.Base using (πGr ; π'Gr ; π'Gr≅πGr ; Ω→SphereMap)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.CW.HurewiczTheorem using (HurewiczHom ; HurewiczMap)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass using (loop-class)

open IsGroupHom using (pres· ; presinv ; pres1)

private
  abstract
    sphere-map-circle : (X : CW₀) (x : fst X) (p : x ≡ x)
      → fst (Ω→SphereMap 1 {A = (fst X , x)} p) ≡ circleMap p
    sphere-map-circle X x p = funExt λ
      { base → refl
      ; (loop i) → refl }

abstract
  -- HurewiczHom has domain π', so transport explicitly from loop-based π.
  loop-hom : (X : CW₀) (cx : isConnected 2 (fst X)) (x : fst X)
    → GroupHom (πGr 0 (fst X , x)) (H̃ᶜʷ X 1)
  loop-hom X cx x = compGroupHom
    {F = πGr 0 (fst X , x)} {G = π'Gr 0 (fst X , x)} {H = H̃ᶜʷ X 1}
    (GroupEquiv→GroupHom
      {G = πGr 0 (fst X , x)} {H = π'Gr 0 (fst X , x)}
      (invGroupEquiv
        {G = π'Gr 0 (fst X , x)} {H = πGr 0 (fst X , x)}
        (GroupIso→GroupEquiv
          {G = π'Gr 0 (fst X , x)} {H = πGr 0 (fst X , x)}
          (π'Gr≅πGr 0 (fst X , x)))))
    (HurewiczHom {n = 0} X x cx)

  loop-hom-eval : (X : CW₀) (cx : isConnected 2 (fst X))
    (x : fst X) (p : x ≡ x)
    → fst (loop-hom X cx x) ∣ p ∣₂ ≡ loop-class X x p
  loop-hom-eval X cx x p =
    -- The inverse π'≅π sends ∣ p ∣₂ to ∣ Ω→SphereMap 1 p ∣₂.
    -- HurewiczMap on that representative is the raw cellular image.
    cong {A = GroupHom (H̃ᶜʷ (Sᶜʷ 1) 1) (H̃ᶜʷ X 1)}
      {B = λ _ → fst (H̃ᶜʷ X 1)} (λ h → fst h (genHₙSⁿ 0))
      (sym (cellular-map-agrees (Sᶜʷ 1) X 1
        (fst (Ω→SphereMap 1 {A = (fst X , x)} p))))
    ∙ cong {A = S¹ → fst X} {B = λ _ → fst (H̃ᶜʷ X 1)}
        (λ f → fst (cellular-map (Sᶜʷ 1) X 1 f) (genHₙSⁿ 0))
        (sphere-map-circle X x p)

abstract
  loop-add : (X : CW₀) (cx : isConnected 2 (fst X))
    (x : fst X) (p q : x ≡ x)
    → loop-class X x (p ∙ q)
      ≡ GroupStr._·_ (snd (H̃ᶜʷ X 1)) (loop-class X x p) (loop-class X x q)
  loop-add X cx x p q = sym (loop-hom-eval X cx x (p ∙ q))
    ∙ pres· (snd (loop-hom X cx x)) ∣ p ∣₂ ∣ q ∣₂
    ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ X 1)))
        (loop-hom-eval X cx x p) (loop-hom-eval X cx x q)

  loop-inv : (X : CW₀) (cx : isConnected 2 (fst X))
    (x : fst X) (p : x ≡ x)
    → loop-class X x (sym p)
      ≡ GroupStr.inv (snd (H̃ᶜʷ X 1)) (loop-class X x p)
  loop-inv X cx x p = sym (loop-hom-eval X cx x (sym p))
    ∙ presinv (snd (loop-hom X cx x)) ∣ p ∣₂
    ∙ cong (GroupStr.inv (snd (H̃ᶜʷ X 1))) (loop-hom-eval X cx x p)

  loop-refl : (X : CW₀) (cx : isConnected 2 (fst X)) (x : fst X)
    → loop-class X x refl ≡ GroupStr.1g (snd (H̃ᶜʷ X 1))
  loop-refl X cx x = sym (loop-hom-eval X cx x refl)
    ∙ pres1 (snd (loop-hom X cx x))
