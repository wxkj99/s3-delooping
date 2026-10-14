{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.CW.Homology.Base using (H̃ᶜʷAb ; H̃ᶜʷ→comp ; H̃ᶜʷ→Equiv)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.CellularPushout.Algebra using (fstHom ; sndHom ; pairHom)
open import DeloopS3.Bridge.DMCExactness.Geometric using (actual-source)

open IsGroupHom

abstract
  map-comp : (X Y Z : CW₀) (n : ℕ) (g : fst Y → fst Z) (f : fst X → fst Y)
    → cellular-map X Z n (g ∘ f)
      ≡ compGroupHom (cellular-map X Y n f) (cellular-map Y Z n g)
  map-comp X Y Z n g f = cellular-map-agrees X Z n (g ∘ f)
    ∙ H̃ᶜʷ→comp {C = X} {D = Y} {E = Z} n g f
    ∙ cong₂ compGroupHom (sym (cellular-map-agrees X Y n f))
        (sym (cellular-map-agrees Y Z n g))

  map-equiv : (X Y : CW₀) (n : ℕ) (e : fst X ≃ fst Y)
    → isEquiv (fst (cellular-map X Y n (equivFun e)))
  map-equiv X Y n e = subst (λ h → isEquiv (fst h))
    (sym (cellular-map-agrees X Y n (equivFun e)))
    (snd (fst (H̃ᶜʷ→Equiv {C = X} {D = Y} n e)))

  map-square : (X Y Z : CW₀) (n : ℕ)
    (f : fst X → fst Y) (g : fst Y → fst Z) (h : fst X → fst Z)
    → g ∘ f ≡ h → (x : fst (H̃ᶜʷ X n))
    → fst (cellular-map Y Z n g) (fst (cellular-map X Y n f) x)
      ≡ fst (cellular-map X Z n h) x
  map-square X Y Z n f g h p x =
    funExt⁻ (cong fst (sym (map-comp X Y Z n g f)
      ∙ cong (cellular-map X Z n) p)) x

  sum-hom : (X Y Z : CW₀) (n : ℕ) (f : fst X → fst Z) (g : fst Y → fst Z)
    → GroupHom (DirProd (H̃ᶜʷ X (suc n)) (H̃ᶜʷ Y (suc n))) (H̃ᶜʷ Z (suc n))
  sum-hom X Y Z n f g = addGroupHom
    (dirProdAb (H̃ᶜʷAb X n) (H̃ᶜʷAb Y n)) (H̃ᶜʷAb Z n)
    (compGroupHom (fstHom (H̃ᶜʷAb X n) (H̃ᶜʷAb Y n)) (cellular-map X Z (suc n) f))
    (compGroupHom (sndHom (H̃ᶜʷAb X n) (H̃ᶜʷAb Y n)) (cellular-map Y Z (suc n) g))

  sum-hom-eval : (X Y Z : CW₀) (n : ℕ) (f : fst X → fst Z) (g : fst Y → fst Z)
    (x : fst (H̃ᶜʷ X (suc n))) (y : fst (H̃ᶜʷ Y (suc n)))
    → fst (sum-hom X Y Z n f g) (x , y)
      ≡ GroupStr._·_ (snd (H̃ᶜʷ Z (suc n)))
        (fst (cellular-map X Z (suc n) f) x) (fst (cellular-map Y Z (suc n) g) y)
  sum-hom-eval X Y Z n f g x y = refl

  signed-hom : (A B C : CW₀) (n : ℕ) (f : fst A → fst B) (g : fst A → fst C)
    → GroupHom (H̃ᶜʷ A (suc n)) (DirProd (H̃ᶜʷ B (suc n)) (H̃ᶜʷ C (suc n)))
  signed-hom A B C n f g = pairHom {X = H̃ᶜʷAb A n} {Y = H̃ᶜʷAb B n} {Z = H̃ᶜʷAb C n}
    (cellular-map A B (suc n) f)
    (negGroupHom (H̃ᶜʷAb A n) (H̃ᶜʷAb C n) (cellular-map A C (suc n) g))

  signed-hom-eval : (A B C : CW₀) (n : ℕ) (f : fst A → fst B) (g : fst A → fst C)
    (a : fst (H̃ᶜʷ A (suc n)))
    → fst (signed-hom A B C n f g) a ≡ actual-source A B C f g (suc n) a
  signed-hom-eval A B C n f g a = refl

  map-sum-value : (X Y S Z : CW₀) (n : ℕ)
    (i : fst X → fst S) (j : fst Y → fst S) (f : fst S → fst Z)
    (u : fst X → fst Z) (v : fst Y → fst Z)
    → f ∘ i ≡ u → f ∘ j ≡ v
    → (x : fst (H̃ᶜʷ X n)) (y : fst (H̃ᶜʷ Y n)) (s : fst (H̃ᶜʷ S n))
    → s ≡ GroupStr._·_ (snd (H̃ᶜʷ S n))
        (fst (cellular-map X S n i) x) (fst (cellular-map Y S n j) y)
    → fst (cellular-map S Z n f) s ≡ GroupStr._·_ (snd (H̃ᶜʷ Z n))
        (fst (cellular-map X Z n u) x) (fst (cellular-map Y Z n v) y)
  map-sum-value X Y S Z n i j f u v pi pj x y s ps =
    cong (fst (cellular-map S Z n f)) ps
    ∙ pres· (snd (cellular-map S Z n f))
        (fst (cellular-map X S n i) x) (fst (cellular-map Y S n j) y)
    ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ Z n)))
        (map-square X S Z n i f u pi x) (map-square Y S Z n j f v pj y)
