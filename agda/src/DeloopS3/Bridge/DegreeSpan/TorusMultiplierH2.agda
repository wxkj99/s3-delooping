{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusMultiplierH2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using
  (GroupHom≡ ; idGroupHom ; trivGroupHom ; compGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using
  (emloop ; emsquash ; emloop-1g)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.CW.Homology.Base using
  (H̃ᶜʷ ; H̃ᶜʷ→ ; H̃ᶜʷ→id ; H̃ᶜʷ→comp)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (torus-H₂ ; torus-square-coordinate)
open import DeloopS3.Bridge.ComponentHomology.Circle using
  (circleCW ; into-circle-H₂-zero)
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T² ; mulC)

-- Scalar actions for multipliers 1 and 0. TorusReflectionH2 treats reflection;
-- TorusIntegerH2 proves the action for every integer.
TorusMultiplierH₂Scalar : ℤ → Type
TorusMultiplierH₂Scalar ℓ = (z : fst (H̃ᶜʷ torusCW 2))
  → torus-square-coordinate
      (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2
        (TorusMultiplier.actual ℓ)) z)
    ≡ ℓ Z.· torus-square-coordinate z

private
  abstract
    mul-one : (a : C) → mulC (pos 1) a ≡ a
    mul-one = elimSet ℤGroup (λ _ → emsquash _ _) refl
      (λ n i j → emloop n i)

    mul-zero : (u : C) → mulC (pos 0) u ≡ 0C
    mul-zero = elimSet ℤGroup (λ _ → emsquash _ _) refl
      (λ g i j → emloop-1g ℤGroup j i)

  project : T² → C
  project = snd

  include : C → T²
  include t = 0C , t

  inclusion-H₂ : GroupHom (H̃ᶜʷ circleCW 2) (H̃ᶜʷ torusCW 2)
  inclusion-H₂ = H̃ᶜʷ→ {C = circleCW} {D = torusCW} 2 include

  abstract
    actual-one : Path (T² → T²)
      (TorusMultiplier.actual (pos 1)) (idfun T²)
    actual-one = funExt λ (u , t) i → mul-one u i , t

    actual-zero : Path (T² → T²)
      (TorusMultiplier.actual (pos 0)) (include ∘ project)
    actual-zero = funExt λ (u , t) i → mul-zero u i , t

    one-hom : Path (GroupHom (H̃ᶜʷ torusCW 2) (H̃ᶜʷ torusCW 2))
      (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2
        (TorusMultiplier.actual (pos 1)))
      idGroupHom
    one-hom =
      cong (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2) actual-one
      ∙ H̃ᶜʷ→id {C = torusCW} 2

    zero-hom : Path (GroupHom (H̃ᶜʷ torusCW 2) (H̃ᶜʷ torusCW 2))
      (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2
        (TorusMultiplier.actual (pos 0)))
      trivGroupHom
    zero-hom =
      cong (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2) actual-zero
      ∙ H̃ᶜʷ→comp {C = torusCW} {D = circleCW} {E = torusCW}
          2 include project
      ∙ cong (λ k → compGroupHom k inclusion-H₂)
          (into-circle-H₂-zero torusCW project)
      ∙ GroupHom≡ (funExt λ z → IsGroupHom.pres1 (snd inclusion-H₂))

abstract
  torus-multiplier-H₂-one : TorusMultiplierH₂Scalar (pos 1)
  torus-multiplier-H₂-one z =
    cong torus-square-coordinate (cong (λ h → fst h z) one-hom)
    ∙ sym (Z.·IdL (torus-square-coordinate z))

  torus-multiplier-H₂-zero : TorusMultiplierH₂Scalar (pos 0)
  torus-multiplier-H₂-zero z =
    cong torus-square-coordinate (cong (λ h → fst h z) zero-hom)
    ∙ IsGroupHom.pres1 (snd torus-H₂)
    ∙ sym (Z.·AnnihilL (torus-square-coordinate z))
