{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.Circle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc ; _+_ ; +-comm)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.CW.Base using (hasCWskel)
open import Cubical.CW.ChainComplex using (∂)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ ; Sᶜʷ ; hasCWskelSphere)
open import Cubical.CW.Homology.Groups.Sn using (HₙSⁿ≅ℤ ; ∂VanishS ; genHₙSⁿ)
open import Cubical.HITs.S1.Base using (S¹)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.ChainTools
open import DeloopS3.Move.CancelMinimal using (C)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)

-- These witnesses refer to the actual circle used by the Seifert span.
finite-equiv : {X Y : Type} {d : ℕ} → X ≃ Y → Finite≤ d Y → Finite≤ d X
finite-equiv e = PT.map λ (s , q) → s , compEquiv e q

S¹-finite : Finite≤ 1 S¹
S¹-finite = sphere-finite≤ 1

C-finite : Finite≤ 1 C
C-finite = finite-equiv (invEquiv S¹≃C) S¹-finite

C-skeleton : hasCWskel C
C-skeleton = Sˢᵏᵉˡ 1 , compEquiv (invEquiv S¹≃C) (snd (hasCWskelSphere 1))

circleCW : CW₀
circleCW = C , PT.∣ C-skeleton ∣₁

S¹CW : CW₀
S¹CW = Sᶜʷ 1

abstract
  circle-cells₀ : snd (Sˢᵏᵉˡ 1) .fst 0 ≡ 1
  circle-cells₀ = refl

  circle-cells₁ : snd (Sˢᵏᵉˡ 1) .fst 1 ≡ 1
  circle-cells₁ = refl

  circle-boundary : (x : Fin 1 → ℤ)
    → fst (∂ (Sˢᵏᵉˡ 1) 0) x ≡ (λ _ → pos 0)
  circle-boundary = ∂VanishS 0 0

  S¹-H₁ : GroupEquiv (H̃ᶜʷ S¹CW 1) ℤGroup
  S¹-H₁ = GroupIso→GroupEquiv (HₙSⁿ≅ℤ 0)

  circle-H₁ : GroupEquiv (H̃ᶜʷ circleCW 1) ℤGroup
  circle-H₁ = compGroupEquiv (chosen-skeleton circleCW C-skeleton 1)
    (GroupIso→GroupEquiv (HₙSⁿ≅ℤ 0))

  S¹-H₀ : Hzero S¹CW 0
  S¹-H₀ = one-vertex-homology (Sˢᵏᵉˡ 1) refl

  circle-H₀ : Hzero circleCW 0
  circle-H₀ = chosen-zero circleCW C-skeleton 0
    (one-vertex-homology (Sˢᵏᵉˡ 1) refl)

  S¹-H-above : (k : ℕ) → 1 < k → Hzero S¹CW k
  S¹-H-above k = finite≤-homology-above S¹CW 1 k S¹-finite

  circle-H-above : (k : ℕ) → 1 < k → Hzero circleCW k
  circle-H-above k = finite≤-homology-above circleCW 1 k C-finite

  circle-H≥2 : (n : ℕ) → Hzero circleCW (2 + n)
  circle-H≥2 n = circle-H-above (2 + n) (n , +-comm n 2)

-- Explicit integer coordinate and its inverse cellular generator.
circle-coordinate : fst (H̃ᶜʷ circleCW 1) → ℤ
circle-coordinate = fst (fst circle-H₁)

circle-generator : fst (H̃ᶜʷ circleCW 1)
circle-generator = invEq (fst circle-H₁) (pos 1)

circle-generator-coordinate : circle-coordinate circle-generator ≡ pos 1
circle-generator-coordinate = secEq (fst circle-H₁) (pos 1)

circle-cell-generator : fst (H̃ᶜʷ circleCW 1)
circle-cell-generator = invEq (fst (chosen-skeleton circleCW C-skeleton 1)) (genHₙSⁿ 0)

abstract
  circle-cell-coordinate : circle-coordinate circle-cell-generator ≡ pos 1
  circle-cell-coordinate = cong (Iso.fun (fst (HₙSⁿ≅ℤ 0)))
    (secEq (fst (chosen-skeleton circleCW C-skeleton 1)) (genHₙSⁿ 0))

  circle-generator-is-cell : circle-generator ≡ circle-cell-generator
  circle-generator-is-cell = cong (invEq (fst circle-H₁)) (sym circle-cell-coordinate)
    ∙ retEq (fst circle-H₁) circle-cell-generator

-- In particular every ACTUAL map into a core circle is zero in degree 2.
abstract
  into-circle-H₂-zero : (X : CW₀) (f : fst X → C)
    → H̃ᶜʷ→ {C = X} {D = circleCW} 2 f ≡ trivGroupHom
  into-circle-H₂-zero X f = GroupHom≡ (funExt λ x →
    isContr→isProp (circle-H≥2 0) _ _)
