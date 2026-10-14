{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFromTorus where

-- Actual boundary columns from the two torus projections and the reflection sign.
-- BoundaryColumnsFinal supplies the sign via TorusReflectionH2.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; isSetℤ)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Sn.Degree using
  (degree ; degree∥₂Iso ; degreeIdfun ; degreeConst)
import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.EilenbergMacLane1.Base using
  (emloop ; emsquash ; emloop-1g)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using
  (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.Finite using
  (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module GraphProduct ; torus-square-coordinate ; graph-square-pair)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T² ; mulC)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-retraction)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
import DeloopS3.Bridge.DegreeSpan.ProjectH2 as Projection
import DeloopS3.Bridge.DegreeSpan.ProjectH2Realization as Project
import DeloopS3.Bridge.DegreeSpan.ReflectedAttachment as Reflection
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)
import DeloopS3.Bridge.DegreeSpan.TorusMultiplierH2 as Multiplier
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns as Base
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof as Adapter
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Statements
  using (ColumnEquations ; RawBoundaryColumnsStatement)
  renaming (BoundaryColumnsStatement to SealedBoundaryColumnsStatement)

-- Generic set-valued and coordinate helpers are elaborated before any
-- substitution of the large actual cellular homology functors.
abstract
  circle-degree-classes : {f g : S¹ → S¹}
    → degree 1 f ≡ degree 1 g → ST.∣ f ∣₂ ≡ ST.∣ g ∣₂
  circle-degree-classes {f} {g} p =
    sym (Iso.ret (degree∥₂Iso 0) ST.∣ f ∣₂)
    ∙ cong (Iso.inv (degree∥₂Iso 0)) p
    ∙ Iso.ret (degree∥₂Iso 0) ST.∣ g ∣₂

  -- degree∥₂Iso's retraction already incorporates degree∥₂≡. Its forward
  -- map computes to degree on ST constructors. There is no PT elimination.
  circle-degree-observable : {A : Type} (setA : isSet A)
    (observe : (S¹ → S¹) → A) {f g : S¹ → S¹}
    → degree 1 f ≡ degree 1 g → observe f ≡ observe g
  circle-degree-observable setA observe {f} {g} p =
    cong (ST.rec setA observe) (circle-degree-classes {f = f} {g = g} p)

  coordinate-map-path : {X A B : Type} (action : X → A → B)
    (coordinate : B → ℤ) {f g : X} → f ≡ g → (z : A)
    → coordinate (action f z) ≡ coordinate (action g z)
  coordinate-map-path action coordinate p z =
    cong (λ f → coordinate (action f z)) p

  coordinate-composition : {A B : Type} (t : A → ℤ) (g : B → ℤ)
    (b : A → B) (p : B → A) (c : A → A)
    → ((w : B) → t (p w) ≡ g w)
    → ((z : A) → c z ≡ p (b z))
    → (z : A) → g (b z) ≡ t (c z)
  coordinate-composition t g b p c projection composition z =
    sym (projection (b z)) ∙ sym (cong t (composition z))

  transport-columns : {A B : Type} (t : A → ℤ) (g : B → ℤ × ℤ)
    {f₁ f₂ f₃ k₁ k₂ k₃ : A → B}
    → f₁ ≡ k₁ → f₂ ≡ k₂ → f₃ ≡ k₃
    → ColumnEquations t g f₁ f₂ f₃ → ColumnEquations t g k₁ k₂ k₃
  transport-columns t g p q r =
    transport (λ i → ColumnEquations t g (p i) (q i) (r i))

-- Conjugate the first circle factor only; the fibre is unchanged.
φ : (S¹ → S¹) → T² → T²
φ f (u , t) = circleToC (f (CToCircle u)) , t

-- The H₂ sign of the explicit first-factor reflection φ Reflection.reflection.
TorusReflectionH₂ : Type
TorusReflectionH₂ = (z : fst (H̃ᶜʷ torusCW 2))
  → torus-square-coordinate
      (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 (φ Reflection.reflection)) z)
    ≡ Z.- torus-square-coordinate z

private
  torus-action : (T² → T²) → fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ torusCW 2)
  torus-action f = fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 f)

  abstract
    mul-one : (u : C) → mulC (pos 1) u ≡ u
    mul-one = elimSet ℤGroup (λ _ → emsquash _ _) refl
      (λ n i j → emloop n i)

    mul-zero : (u : C) → mulC (pos 0) u ≡ 0C
    mul-zero = elimSet ℤGroup (λ _ → emsquash _ _) refl
      (λ n i j → emloop-1g ℤGroup j i)

    φ-one : φ (idfun S¹) ≡ TorusMultiplier.actual (pos 1)
    φ-one = funExt λ (u , t) i →
      (circle-retraction u ∙ sym (mul-one u)) i , t

    φ-zero : φ (λ _ → base) ≡ TorusMultiplier.actual (pos 0)
    φ-zero = funExt λ (u , t) i → mul-zero u (~ i) , t

abstract
  circle-action-degree : {f g : S¹ → S¹}
    → degree 1 f ≡ degree 1 g → (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate (torus-action (φ f) z)
      ≡ torus-square-coordinate (torus-action (φ g) z)
  circle-action-degree {f} {g} p z = circle-degree-observable isSetℤ
    (λ h → torus-square-coordinate (torus-action (φ h) z)) {f = f} {g = g} p

  circle-action-one : (f : S¹ → S¹) → degree 1 f ≡ pos 1
    → (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate (torus-action (φ f) z) ≡ torus-square-coordinate z
  circle-action-one f p z =
    circle-action-degree {f = f} {g = idfun S¹} (p ∙ sym (degreeIdfun 1)) z
    ∙ coordinate-map-path torus-action torus-square-coordinate φ-one z
    ∙ Multiplier.torus-multiplier-H₂-one z
    ∙ Z.·IdL (torus-square-coordinate z)

  circle-action-zero : (f : S¹ → S¹) → degree 1 f ≡ pos 0
    → (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate (torus-action (φ f) z) ≡ pos 0
  circle-action-zero f p z =
    circle-action-degree {f = f} {g = λ _ → base} (p ∙ sym (degreeConst 1)) z
    ∙ coordinate-map-path torus-action torus-square-coordinate φ-zero z
    ∙ Multiplier.torus-multiplier-H₂-zero z
    ∙ Z.·AnnihilL (torus-square-coordinate z)

  circle-action-negative : TorusReflectionH₂
    → (f : S¹ → S¹) → degree 1 f ≡ negsuc 0
    → (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate (torus-action (φ f) z) ≡ Z.- torus-square-coordinate z
  circle-action-negative negative f p z =
    circle-action-degree {f = f} {g = Reflection.reflection}
      (p ∙ sym Reflection.reflection-degree) z ∙ negative z

-- These are the literal maps, not cellular representatives chosen in charts.
boundary : (C → Literal.P) → T² → Literal.Core
boundary d (u , t) = d u , t

selected-word : Fin 2 → (C → Literal.P) → S¹ → S¹
selected-word j d = pickPetal j ∘ Words.word-chart ∘ d ∘ circleToC

private
  boundary-action : (C → Literal.P)
    → fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ graph×circleCW 2)
  boundary-action d = fst (H̃ᶜʷ→ {C = torusCW} {D = graph×circleCW} 2 (boundary d))

  projection-action : Fin 2
    → fst (H̃ᶜʷ graph×circleCW 2) → fst (H̃ᶜʷ torusCW 2)
  projection-action j = fst (H̃ᶜʷ→ {C = graph×circleCW} {D = torusCW}
    2 (Projection.project j))

  abstract
    selected-word-agrees : (j : Fin 2) (d : C → Literal.P)
      → φ (selected-word j d) ≡ Projection.project j ∘ boundary d
    selected-word-agrees j d = funExt λ (u , t) i →
      circleToC (pickPetal j (Words.word-chart (d (circle-retraction u i)))) , t

    boundary-composition : (j : Fin 2) (d : C → Literal.P)
      (z : fst (H̃ᶜʷ torusCW 2))
      → torus-action (Projection.project j ∘ boundary d) z
        ≡ projection-action j (boundary-action d z)
    boundary-composition j d z = cong (λ h → fst h z)
      (H̃ᶜʷ→comp {C = torusCW} {D = graph×circleCW} {E = torusCW}
        2 (Projection.project j) (boundary d))

abstract
  -- Project first, then classify the actual first-factor circle map. Each
  -- petal is recovered independently; no equality of coordinate sums is used.
  boundary-coordinate : (j : Fin 2) (d : C → Literal.P)
    (z : fst (H̃ᶜʷ torusCW 2))
    → GraphProduct.square-coordinate (boundary-action d z) j
      ≡ torus-square-coordinate (torus-action (φ (selected-word j d)) z)
  boundary-coordinate j d z =
    coordinate-composition torus-square-coordinate
      (λ w → GraphProduct.square-coordinate w j)
      (boundary-action d) (projection-action j)
      (torus-action (Projection.project j ∘ boundary d))
      (Project.project-H₂ j) (boundary-composition j d) z
    ∙ coordinate-map-path torus-action torus-square-coordinate
        (sym (selected-word-agrees j d)) z

  -- The first two columns are independent of the reflection sign.
  boundary₁-column : (z : fst (H̃ᶜʷ torusCW 2))
    → graph-square-pair (boundary-action Literal.d₁ z)
      ≡ (torus-square-coordinate z , pos 0)
  boundary₁-column z = ΣPathP
    ( boundary-coordinate fzero Literal.d₁ z
      ∙ circle-action-one (selected-word fzero Literal.d₁) Words.d₁-degree-a z
    , boundary-coordinate (fsuc fzero) Literal.d₁ z
      ∙ circle-action-zero (selected-word (fsuc fzero) Literal.d₁) Words.d₁-degree-b z )

  boundary₂-column : (z : fst (H̃ᶜʷ torusCW 2))
    → graph-square-pair (boundary-action Literal.d₂ z)
      ≡ (pos 0 , torus-square-coordinate z)
  boundary₂-column z = ΣPathP
    ( boundary-coordinate fzero Literal.d₂ z
      ∙ circle-action-zero (selected-word fzero Literal.d₂) Words.d₂-degree-a z
    , boundary-coordinate (fsuc fzero) Literal.d₂ z
      ∙ circle-action-one (selected-word (fsuc fzero) Literal.d₂) Words.d₂-degree-b z )

  boundary₃-column : TorusReflectionH₂ → (z : fst (H̃ᶜʷ torusCW 2))
    → graph-square-pair (boundary-action Literal.d₃ z)
      ≡ (Z.- torus-square-coordinate z , Z.- torus-square-coordinate z)
  boundary₃-column negative z = ΣPathP
    ( boundary-coordinate fzero Literal.d₃ z
      ∙ circle-action-negative negative (selected-word fzero Literal.d₃) Words.d₃-degree-a z
    , boundary-coordinate (fsuc fzero) Literal.d₃ z
      ∙ circle-action-negative negative (selected-word (fsuc fzero) Literal.d₃) Words.d₃-degree-b z )

  boundary-columns : TorusReflectionH₂ → RawBoundaryColumnsStatement
  ColumnEquations.boundary₁-column (boundary-columns negative) = boundary₁-column
  ColumnEquations.boundary₂-column (boundary-columns negative) = boundary₂-column
  ColumnEquations.boundary₃-column (boundary-columns negative) = boundary₃-column negative

  raw-to-sealed : RawBoundaryColumnsStatement → SealedBoundaryColumnsStatement
  raw-to-sealed = transport-columns torus-square-coordinate graph-square-pair
    (sym (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₁)))
    (sym (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₂)))
    (sym (cong fst (cellular-map-agrees torusCW graph×circleCW 2 Literal.boundary₃)))

  boundary-columns-sealed : TorusReflectionH₂ → SealedBoundaryColumnsStatement
  boundary-columns-sealed negative = raw-to-sealed (boundary-columns negative)

  base-seifert-boundary-columns : TorusReflectionH₂ → Base.BoundaryColumns
  base-seifert-boundary-columns negative =
    Adapter.to-base-seifert (boundary-columns-sealed negative)
