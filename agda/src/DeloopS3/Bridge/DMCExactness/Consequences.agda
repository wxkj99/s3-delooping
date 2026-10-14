{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Consequences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import DeloopS3.Bridge.CofibreHomology
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.DMCExactness.Groups

-- Pure consequences of a supplied CofibreLES, NOT constructors of that
-- geometric LES. All the group reasoning is isolated in Groups.agda.
abstract
  cofib-H₄-H₅ : (A B Cf : CW₀) (f : fst A → fst B)
    → CofibreLES A B f Cf
    → Hiso A B 3 f → Hzero B 4 → Hzero B 5 → Hzero A 4
    → Hzero Cf 4 × Hzero Cf 5
  cofib-H₄-H₅ A B Cf f les ef b4 b5 a4 =
    exact-zero-middle-injective (L.inclusion-induced 4) (L.boundary 3) (L.map-induced 3)
      (L.exact-cofibre 3 (1 , refl)) (L.exact-source 3 (1 , refl)) b4
      (subst (λ u → isEquiv (fst u)) (sym (L.map-induced-agrees 3)) ef) ,
    exact-zero-middle (L.inclusion-induced 5) (L.boundary 4)
      (L.exact-cofibre 4 (0 , refl)) b5 a4
    where module L = CofibreLES A B f Cf les

  bottom-cofib-homology : (X F : CW₀) (a : BottomMoore → fst X)
    (les : CofibreLES bottomCW X a F) → Hiso bottomCW X 2 a
    → Hzero X 4
    → Hzero F 2 × Hiso X F 3 (CofibreLES.inclusion bottomCW X a F les) × Hzero F 4
  bottom-cofib-homology X F a les ea x4 =
    exact-zero-map-middle (L.inclusion-induced 2) (L.boundary 1)
      (L.exact-cofibre 1 (3 , refl))
      (exact-after-equiv-zero {u = L.map-induced 2} {v = L.inclusion-induced 2}
        (L.exact-target 2 (2 , refl)) e₂)
      (λ x → contr→zero (H̃ᶜʷ bottomCW 1) bottom-H₁ (fst (L.boundary 1) x)) ,
    subst (λ u → isEquiv (fst u)) (L.inclusion-induced-agrees 3)
      (exact-middle-equiv (L.map-induced 3) (L.inclusion-induced 3) (L.boundary 2) (L.map-induced 2)
        (L.exact-target 3 (1 , refl)) (L.exact-cofibre 2 (2 , refl))
        (L.exact-source 2 (2 , refl)) (bottom-H≥3 0) e₂) ,
    exact-zero-middle (L.inclusion-induced 4) (L.boundary 3)
      (L.exact-cofibre 3 (1 , refl)) x4 (bottom-H≥3 0)
    where
    module L = CofibreLES bottomCW X a F les
    e₂ : isEquiv (fst (L.map-induced 2))
    e₂ = subst (λ u → isEquiv (fst u)) (sym (L.map-induced-agrees 2)) ea
