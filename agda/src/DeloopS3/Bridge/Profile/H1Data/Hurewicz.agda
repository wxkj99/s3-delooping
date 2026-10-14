{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Hurewicz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed using (_→∙_)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base using (η)
open import Cubical.Algebra.Group.Abelianization.Properties
  using (AbelianizationGroup ; AbelianizationFun ; AbelianizationEquiv ; elimProp)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base using (πGr ; π'Gr ; π'Gr≅πGr ; π'∘∙Hom)
open import Cubical.CW.HurewiczTheorem using
  (HurewiczHomAb ; HurewiczTheorem ; HurewiczMapNat)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)

-- Degree one DOES retain abelianization. No simply-connected hypothesis.
abstract
  degree1-Hurewicz' : (X : CW₀) (conn : isConnected 2 (fst X)) (x : fst X)
    → GroupEquiv (AbelianizationGroup (π'Gr 0 (fst X , x))) (H̃ᶜʷ X 1)
  degree1-Hurewicz' X conn x =
    (fst (HurewiczHomAb X x conn 0) ,
      subst (λ c → isEquiv (fst (HurewiczHomAb X x c 0)))
        (isPropIsContr (isConnectedSubtr' 0 2 conn) conn)
        (HurewiczTheorem 0 X conn x)) , snd (HurewiczHomAb X x conn 0)

  degree1-Hurewicz : (X : CW₀) (conn : isConnected 2 (fst X)) (x : fst X)
    → GroupEquiv (AbelianizationGroup (πGr 0 (fst X , x))) (H̃ᶜʷ X 1)
  degree1-Hurewicz X conn x = compGroupEquiv
    (AbelianizationEquiv (invGroupEquiv (GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst X , x)))))
    (degree1-Hurewicz' X conn x)

  -- Kept at the library's sphere-map convention, with both pointings
  -- explicit. π'Gr≅πGr is not silently treated as definitional equality.
  degree1-natural : (X Y : CW₀)
    (cx : isConnected 2 (fst X)) (cy : isConnected 2 (fst Y))
    (x : fst X) (y : fst Y) (f : (fst X , x) →∙ (fst Y , y))
    (a : fst (AbelianizationGroup (π'Gr 0 (fst X , x))))
    → fst (H̃ᶜʷ→ {C = X} {D = Y} 1 (fst f))
        (fst (HurewiczHomAb X x cx 0) a)
      ≡ fst (HurewiczHomAb Y y cy 0)
        (fst (AbelianizationFun (π'∘∙Hom 0 f)) a)
  degree1-natural X Y cx cy x y f = elimProp (π'Gr 0 (fst X , x))
    (λ _ → GroupStr.is-set (snd (H̃ᶜʷ Y 1)) _ _)
    (funExt⁻ (HurewiczMapNat {n = 0} X Y x y f))

open import Cubical.Foundations.Univalence using (ua-gluePath ; ua-ungluePath)
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.Homotopy.Group.Base using (πHom ; GroupHomπ≅π'PathP-hom)

abstract
  -- Generic SIP square, proved before instantiating the large π groups.
  hom-square-along-equivalences : {A B C D : Group₀}
    (eA : GroupEquiv A C) (eB : GroupEquiv B D)
    (f : GroupHom A B) (g : GroupHom C D)
    → PathP (λ i → GroupHom (fst (GroupPath A C) eA i) (fst (GroupPath B D) eB i)) f g
    → (a : fst A) → equivFun (fst eB) (fst f a) ≡ fst g (equivFun (fst eA) a)
  hom-square-along-equivalences eA eB f g p a = ua-ungluePath (fst eB)
    (λ i → fst (p i) (ua-gluePath (fst eA) {x = a} refl i))

  π-loop-sphere-natural : (X Y : CW₀) (x : fst X) (y : fst Y)
    (f : (fst X , x) →∙ (fst Y , y)) (a : fst (πGr 0 (fst X , x)))
    → fst (π'∘∙Hom 0 f) (invEq (fst (GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst X , x)))) a)
      ≡ invEq (fst (GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst Y , y)))) (fst (πHom 0 f) a)
  π-loop-sphere-natural X Y x y f a = sym (retEq (fst eY) (fst (π'∘∙Hom 0 f) (invEq (fst eX) a)))
    ∙ cong (invEq (fst eY))
      (hom-square-along-equivalences eX eY (π'∘∙Hom 0 f) (πHom 0 f)
        (λ i → GroupHomπ≅π'PathP-hom 0 f (~ i)) (invEq (fst eX) a)
        ∙ cong (fst (πHom 0 f)) (secEq (fst eX) a))
    where
    eX : GroupEquiv (π'Gr 0 (fst X , x)) (πGr 0 (fst X , x))
    eX = GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst X , x))
    eY : GroupEquiv (π'Gr 0 (fst Y , y)) (πGr 0 (fst Y , y))
    eY = GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst Y , y))

  degree1-loop-natural : (X Y : CW₀)
    (cx : isConnected 2 (fst X)) (cy : isConnected 2 (fst Y))
    (x : fst X) (y : fst Y) (f : (fst X , x) →∙ (fst Y , y))
    (a : fst (AbelianizationGroup (πGr 0 (fst X , x))))
    → fst (H̃ᶜʷ→ {C = X} {D = Y} 1 (fst f))
        (equivFun (fst (degree1-Hurewicz X cx x)) a)
      ≡ equivFun (fst (degree1-Hurewicz Y cy y)) (fst (AbelianizationFun (πHom 0 f)) a)
  degree1-loop-natural X Y cx cy x y f a = degree1-natural X Y cx cy x y f (fst pullX a)
    ∙ cong (fst (HurewiczHomAb Y y cy 0)) (commute a)
    where
    pullX : GroupHom (AbelianizationGroup (πGr 0 (fst X , x))) (AbelianizationGroup (π'Gr 0 (fst X , x)))
    pullX = AbelianizationFun (GroupEquiv→GroupHom (invGroupEquiv (GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst X , x)))))
    pullY : GroupHom (AbelianizationGroup (πGr 0 (fst Y , y))) (AbelianizationGroup (π'Gr 0 (fst Y , y)))
    pullY = AbelianizationFun (GroupEquiv→GroupHom (invGroupEquiv (GroupIso→GroupEquiv (π'Gr≅πGr 0 (fst Y , y)))))
    commute : (a : fst (AbelianizationGroup (πGr 0 (fst X , x))))
      → fst (AbelianizationFun (π'∘∙Hom 0 f)) (fst pullX a)
        ≡ fst pullY (fst (AbelianizationFun (πHom 0 f)) a)
    commute = elimProp (πGr 0 (fst X , x))
      (λ _ → GroupStr.is-set (snd (AbelianizationGroup (π'Gr 0 (fst Y , y)))) _ _)
      (λ u → cong η (π-loop-sphere-natural X Y x y f u))
