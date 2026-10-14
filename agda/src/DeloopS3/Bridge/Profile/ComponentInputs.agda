{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.ComponentInputs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun ; idEquiv)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.Group using (Group₀ ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.DirProd using (DirProd)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; isCW ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.DMCExactness.Geometric using (actual-source)
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ⁶ ; vertex₁ ; Araw)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (overlapCW ; fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates using (overlap-H₁ ; vertices-H₁)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof
  using (HurewiczChartIdentification ; degree-one-comparison)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns
  using (BoundaryColumns ; boundary-columns→degree-two)
import DeloopS3.Bridge.Profile.BaseSeifert.H0Tail as H0Tail
import DeloopS3.Bridge.Profile.BaseSeifert.Cases as Cases
open import DeloopS3.Bridge.Profile.H1Data.Coordinates using (H1CoordinateData)
open import DeloopS3.Bridge.Profile.H1Data.Components
  using (FourInputs ; ComponentH1Inputs ; ComponentH1Groups ; components-from-inner-MV)
open import DeloopS3.Bridge.Profile.H1Data.PiecesH2 using (pullback-H₂-zero)
open import DeloopS3.Bridge.Profile.H1Data.Actual using (ACW ; CCW)
import DeloopS3.Bridge.Profile.H1Data.Inner as Inner
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Cert.Interpret.Short using (ShortCase)

-- Elaborate the dependent record on arbitrary groups, before specializing
-- to actual cellular homology (whose implementation is deliberately opaque).
private
  coordinate-data : (O₁ V₁ O₀ V₀ : Group₀)
    (s₁ : fst O₁ → fst V₁) (s₀ : fst O₀ → fst V₀) (q n : ℤ)
    (eO : GroupEquiv O₁ (AbGroup→Group ℤ⁶))
    (eV : GroupEquiv V₁ (AbGroup→Group vertex₁))
    → ((a : fst O₁) → fst (Araw (pos 2) q n) (equivFun (fst eO) a)
        ≡ equivFun (fst eV) (s₁ a))
    → ((a : fst O₀) → s₀ a ≡ GroupStr.1g (snd V₀)
        → a ≡ GroupStr.1g (snd O₀))
    → H1CoordinateData O₁ V₁ O₀ V₀ s₁ s₀ q n
  coordinate-data O₁ V₁ O₀ V₀ s₁ s₀ q n eO eV square tail = record
    { overlap-coordinates = eO
    ; vertices = eV
    ; matrix-square = square
    ; zero-tail = tail
    }

  four-inputs : (A B C D : Type₀) → A → B → C → D → FourInputs A B C D
  four-inputs A B C D a b c d = record
    { source-O = a ; source-I = b ; target-O = c ; target-I = d }

module ForInner (q n : ℤ) where
  private
    module I = Inner.Inner q n
    module S = Literal.Seifert (pos 2) q n

  left-with : isCW Literal.Core → CW₀
  left-with w = Literal.Core , w

  -- This family varies the CW witness everywhere, including both actual
  -- signed source maps. Transporting only vertices would lose their squares.
  CoordinatesAt : isCW Literal.Core → Type₀
  CoordinatesAt w = H1CoordinateData
    (H̃ᶜʷ overlapCW 1)
    (DirProd (H̃ᶜʷ (left-with w) 1) (H̃ᶜʷ fillingsCW 1))
    (H̃ᶜʷ overlapCW 0)
    (DirProd (H̃ᶜʷ (left-with w) 0) (H̃ᶜʷ fillingsCW 0))
    (actual-source overlapCW (left-with w) fillingsCW S.allLeft S.allRight 1)
    (actual-source overlapCW (left-with w) fillingsCW S.allLeft S.allRight 0) q n

  -- Explicit endpoints: only the left witness changes. No equality of
  -- individual coordinate fields is asserted or needed.
  overlap-endpoint : overlapCW ≡ I.overlapCW
  overlap-endpoint = refl

  fillings-endpoint : fillingsCW ≡ I.rightCW
  fillings-endpoint = refl

  graph-endpoint : left-with (snd graph×circleCW) ≡ graph×circleCW
  graph-endpoint = refl

  left-endpoint : left-with (snd I.leftCW) ≡ I.leftCW
  left-endpoint = refl

  coordinates-endpoint : CoordinatesAt (snd I.leftCW) ≡ I.H1Coordinates
  coordinates-endpoint = refl

  abstract
    -- Before transport, these are exactly the BaseSeifert charts.
    -- DegreeOneComparison has the opposite orientation to matrix-square.
    graph-coordinates : HurewiczChartIdentification
      → CoordinatesAt (snd graph×circleCW)
    graph-coordinates markings = coordinate-data
      (H̃ᶜʷ overlapCW 1)
      (DirProd (H̃ᶜʷ graph×circleCW 1) (H̃ᶜʷ fillingsCW 1))
      (H̃ᶜʷ overlapCW 0)
      (DirProd (H̃ᶜʷ graph×circleCW 0) (H̃ᶜʷ fillingsCW 0))
      (actual-source overlapCW graph×circleCW fillingsCW S.allLeft S.allRight 1)
      (actual-source overlapCW graph×circleCW fillingsCW S.allLeft S.allRight 0)
      q n overlap-H₁ vertices-H₁
      (λ a → sym (degree-one-comparison markings (pos 2) q n a))
      (H0Tail.zero-tail (pos 2) q n)

    -- Transport the WHOLE record, not fieldwise equalities between charts.
    transported-coordinates : HurewiczChartIdentification → I.H1Coordinates
    transported-coordinates markings = subst CoordinatesAt
      (PT.squash₁ (snd graph×circleCW) (snd I.leftCW))
      (graph-coordinates markings)

    -- Reuse the exact, unconditional Inner H0 tail. The H1 fields all come
    -- from the full witness transport above, including its actual-source.
    inner-coordinates : HurewiczChartIdentification → I.H1Coordinates
    inner-coordinates markings = coordinate-data
      (H̃ᶜʷ I.overlapCW 1)
      (DirProd (H̃ᶜʷ I.leftCW 1) (H̃ᶜʷ I.rightCW 1))
      (H̃ᶜʷ I.overlapCW 0)
      (DirProd (H̃ᶜʷ I.leftCW 0) (H̃ᶜʷ I.rightCW 0))
      (actual-source I.overlapCW I.leftCW I.rightCW S.allLeft S.allRight 1)
      (actual-source I.overlapCW I.leftCW I.rightCW S.allLeft S.allRight 0)
      q n D.overlap-coordinates D.vertices D.matrix-square
      (H0Tail.InnerTail.inner-zero-tail q n)
      where
      module D = H1CoordinateData (transported-coordinates markings)

-- The four EXISTING Inner endpoints used by ComponentH1Inputs.
module SourceO = ForInner (pos 2) (pos 4)
module SourceI = ForInner (pos 2) (pos 3)
module TargetO = ForInner (pos 3) (pos 4)
module TargetI = ForInner (pos 3) (pos 5)

abstract
  component-H₁-inputs : HurewiczChartIdentification → ComponentH1Inputs
  component-H₁-inputs markings = four-inputs
    (Inner.Inner.H1Coordinates (pos 2) (pos 4))
    (Inner.Inner.H1Coordinates (pos 2) (pos 3))
    (Inner.Inner.H1Coordinates (pos 3) (pos 4))
    (Inner.Inner.H1Coordinates (pos 3) (pos 5))
    (SourceO.inner-coordinates markings) (SourceI.inner-coordinates markings)
    (TargetO.inner-coordinates markings) (TargetI.inner-coordinates markings)

  -- All finite-group algebra stays in the existing H1Data consumers.
  component-H₁-groups : HurewiczChartIdentification → PT.∥ ComponentH1Groups ∥₁
  component-H₁-groups markings = components-from-inner-MV (component-H₁-inputs markings)

-- Actual-space endpoints for the H2 change of CW witness. These are literal
-- original components, not a replacement homology model.
source-endpoint : (c : ShortCase) → fst (ACW c) ≡ fst (Cases.sourceCW c)
source-endpoint c = refl

target-endpoint : (c : ShortCase) → fst (CCW c) ≡ fst (Cases.baseCW c)
target-endpoint c = refl

abstract
  -- Cases already supplies the necessary MV exactness and matrix kernels.
  -- No separate ComponentH2Inputs premise, and no H3 coordinates, are added.
  source-H₂-zero : HurewiczChartIdentification → BoundaryColumns
    → (c : ShortCase) → Hzero (ACW c) 2
  source-H₂-zero markings columns c =
    pullback-H₂-zero (ACW c) (Cases.sourceCW c) (idEquiv (fst (ACW c)))
      (Cases.source-H₂-from-matrices c
        (boundary-columns→degree-two columns (pos 2) (pos 2) (Cases.source-r c))
        (degree-one-comparison markings (pos 2) (pos 2) (Cases.source-r c)))

  target-H₂-zero : HurewiczChartIdentification → BoundaryColumns
    → (c : ShortCase) → Hzero (CCW c) 2
  target-H₂-zero markings columns c =
    pullback-H₂-zero (CCW c) (Cases.baseCW c) (idEquiv (fst (CCW c)))
      (Cases.base-H₂-from-matrices c
        (boundary-columns→degree-two columns (pos 2) (pos 3) (Cases.base-r c))
        (degree-one-comparison markings (pos 2) (pos 3) (Cases.base-r c)))
