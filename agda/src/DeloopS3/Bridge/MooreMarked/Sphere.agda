{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.MooreMarked.Sphere where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.Data.Int using (ℤ ; pos ; isSetℤ ; ·IdR ; ·Comm)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction using (ℤHomId ; GroupHomℤ→ℤPres·)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn ; sphereConnected)
open import Cubical.HITs.Sn.Degree using (degree ; degree∥₂Iso ; degreeHom ; degreeIdfun)
open import Cubical.Homotopy.Group.Base using (π'Gr)
open import Cubical.Homotopy.Group.PinSn using (πₙSⁿ-unpointIso)
open import Cubical.Homotopy.Connected using
  (isConnectedSubtr' ; isConnectedPath)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (HₙSⁿ≅ℤ ; genHₙSⁿ)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→id)
open import Cubical.CW.HurewiczTheorem using (HurewiczHom ; HurewiczMapUntrunc)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as TR

opaque
  sphereCoordinates : (k : ℕ)
    → GroupEquiv (H̃ᶜʷ (Sᶜʷ (2 + k)) (2 + k)) ℤGroup
  sphereCoordinates k = GroupIso→GroupEquiv (HₙSⁿ≅ℤ (suc k))

sphereCoordinate : (k : ℕ) → fst (H̃ᶜʷ (Sᶜʷ (2 + k)) (2 + k)) → ℤ
sphereCoordinate k = equivFun (fst (sphereCoordinates k))

opaque
  unfolding sphereCoordinates
  sphereCoordinate-generator : (k : ℕ)
    → sphereCoordinate k (genHₙSⁿ (suc k)) ≡ pos 1
  sphereCoordinate-generator k = refl

private
  opaque
    degree-equivalence : (k : ℕ) → GroupEquiv (π'Gr (suc k) (S₊∙ (2 + k))) ℤGroup
    fst (degree-equivalence k) = isoToEquiv
      (compIso (πₙSⁿ-unpointIso (suc k)) (degree∥₂Iso (suc k)))
    snd (degree-equivalence k) = makeIsGroupHom
      (ST.elim2 (λ _ _ → isProp→isSet (isSetℤ _ _)) (degreeHom {n = suc k}))

  opaque
    unfolding degree-equivalence
    degree-equivalence-value : (k : ℕ) (f : S₊∙ (2 + k) →∙ S₊∙ (2 + k))
      → equivFun (fst (degree-equivalence k)) ST.∣ f ∣₂ ≡ degree (2 + k) (fst f)
    degree-equivalence-value k f = refl

    degree-equivalence-id : (k : ℕ)
      → equivFun (fst (degree-equivalence k)) ST.∣ idfun∙ (S₊∙ (2 + k)) ∣₂ ≡ pos 1
    degree-equivalence-id k = degreeIdfun (2 + k)

  abstract
    coordinate-unique : (G : Group₀) (e : GroupEquiv G ℤGroup)
      (g : fst G) (mark : equivFun (fst e) g ≡ pos 1)
      (f : GroupHom G ℤGroup) → fst f g ≡ pos 1
      → fst f ≡ equivFun (fst e)
    coordinate-unique G e g mark f value = funExt λ x →
      cong (fst f) (sym (retEq (fst e) x))
      ∙ funExt⁻ (ℤHomId conjugate fixes) (equivFun (fst e) x)
      where
      conjugate : GroupHom ℤGroup ℤGroup
      conjugate = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv e)) f
      fixes : fst conjugate (pos 1) ≡ pos 1
      fixes = cong (fst f) (cong (invEq (fst e)) (sym mark) ∙ retEq (fst e) g) ∙ value

  opaque
    hurewicz-coordinate : (k : ℕ)
      → GroupHom (π'Gr (suc k) (S₊∙ (2 + k))) ℤGroup
    hurewicz-coordinate k = compGroupHom
      (HurewiczHom {n = suc k} (Sᶜʷ (2 + k)) (ptSn (2 + k))
        (isConnectedSubtr' (suc k) 2 (sphereConnected (2 + k))))
      (GroupEquiv→GroupHom (sphereCoordinates k))

  opaque
    unfolding hurewicz-coordinate
    hurewicz-coordinate-value : (k : ℕ) (f : S₊∙ (2 + k) →∙ S₊∙ (2 + k))
      → fst (hurewicz-coordinate k) ST.∣ f ∣₂
        ≡ sphereCoordinate k (HurewiczMapUntrunc {n = suc k}
            (Sᶜʷ (2 + k)) (ptSn (2 + k)) f)
    hurewicz-coordinate-value k f = refl

    hurewicz-coordinate-id : (k : ℕ)
      → fst (hurewicz-coordinate k) ST.∣ idfun∙ (S₊∙ (2 + k)) ∣₂ ≡ pos 1
    hurewicz-coordinate-id k = cong (sphereCoordinate k)
      (funExt⁻ (cong fst (H̃ᶜʷ→id {C = Sᶜʷ (2 + k)} (2 + k))) (genHₙSⁿ (suc k)))
      ∙ sphereCoordinate-generator k

  abstract
    hurewicz-degree : (k : ℕ) (f : S₊∙ (2 + k) →∙ S₊∙ (2 + k))
      → sphereCoordinate k (HurewiczMapUntrunc {n = suc k}
          (Sᶜʷ (2 + k)) (ptSn (2 + k)) f) ≡ degree (2 + k) (fst f)
    hurewicz-degree k f = sym (hurewicz-coordinate-value k f)
      ∙ funExt⁻ (coordinate-unique (π'Gr (suc k) (S₊∙ (2 + k)))
        (degree-equivalence k) ST.∣ idfun∙ (S₊∙ (2 + k)) ∣₂
        (degree-equivalence-id k) (hurewicz-coordinate k) (hurewicz-coordinate-id k)) ST.∣ f ∣₂
      ∙ degree-equivalence-value k f

  abstract
    homology-degree-generator : (k : ℕ) (f : S₊ (2 + k) → S₊ (2 + k))
      → sphereCoordinate k
          (fst (H̃ᶜʷ→ {C = Sᶜʷ (2 + k)} {D = Sᶜʷ (2 + k)} (2 + k) f)
            (genHₙSⁿ (suc k))) ≡ degree (2 + k) f
    homology-degree-generator k f = TR.rec {n = 1} (isSetℤ _ _) at-point pointing
      where
      Goal : Type
      Goal = sphereCoordinate k
        (fst (H̃ᶜʷ→ {C = Sᶜʷ (2 + k)} {D = Sᶜʷ (2 + k)} (2 + k) f)
          (genHₙSⁿ (suc k))) ≡ degree (2 + k) f
      at-point : f (ptSn (2 + k)) ≡ ptSn (2 + k) → Goal
      at-point p = hurewicz-degree k (f , p)
      pointing : TR.hLevelTrunc 1 (f (ptSn (2 + k)) ≡ ptSn (2 + k))
      pointing = fst (isConnectedPath 1
        (isConnectedSubtr' (suc k) 2 (sphereConnected (2 + k)))
        (f (ptSn (2 + k))) (ptSn (2 + k)))

  abstract
    coordinate-linear : (G : Group₀) (e : GroupEquiv G ℤGroup)
      (u : fst G) (d : ℤ) (action : GroupHom G G)
      → equivFun (fst e) u ≡ pos 1
      → equivFun (fst e) (fst action u) ≡ d
      → (z : fst G)
      → equivFun (fst e) (fst action z) ≡ d Z.· equivFun (fst e) z
    coordinate-linear G e u d action mark value z =
      cong (λ t → equivFun (fst e) (fst action t)) (sym (retEq (fst e) z))
      ∙ cong (fst conjugate) (sym (·IdR (equivFun (fst e) z)))
      ∙ GroupHomℤ→ℤPres· conjugate (equivFun (fst e) z) (pos 1)
      ∙ cong (equivFun (fst e) z Z.·_) one
      ∙ ·Comm (equivFun (fst e) z) d
      where
      conjugate : GroupHom ℤGroup ℤGroup
      conjugate = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv e))
        (compGroupHom action (GroupEquiv→GroupHom e))
      one : fst conjugate (pos 1) ≡ d
      one = cong (λ t → equivFun (fst e) (fst action t))
        (cong (invEq (fst e)) (sym mark) ∙ retEq (fst e) u) ∙ value

abstract
  sphere-homology-degree : (k : ℕ) (f : S₊ (2 + k) → S₊ (2 + k))
    (z : fst (H̃ᶜʷ (Sᶜʷ (2 + k)) (2 + k)))
    → sphereCoordinate k
        (fst (H̃ᶜʷ→ {C = Sᶜʷ (2 + k)} {D = Sᶜʷ (2 + k)} (2 + k) f) z)
      ≡ degree (2 + k) f Z.· sphereCoordinate k z
  sphere-homology-degree k f = coordinate-linear
    (H̃ᶜʷ (Sᶜʷ (2 + k)) (2 + k)) (sphereCoordinates k)
    (genHₙSⁿ (suc k)) (degree (2 + k) f)
    (H̃ᶜʷ→ {C = Sᶜʷ (2 + k)} {D = Sᶜʷ (2 + k)} (2 + k) f)
    (sphereCoordinate-generator k) (homology-degree-generator k f)
