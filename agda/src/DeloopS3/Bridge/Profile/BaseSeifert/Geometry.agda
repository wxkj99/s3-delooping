{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Geometry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.DirProd
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging
  using (PushoutLES ; finite-pushoutLES-merely)
import DeloopS3.Bridge.SpanCells as Cells
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Move.CancelMinimal using (C ; T²)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

-- The original grouped diagram; these endpoint types are definitionally
-- the HITs from Definition.agda, not replacement presentation spaces.
overlapCW fillingsCW : CW₀
overlapCW = ((T² ⊎ T²) ⊎ T²) , finite≤→isCW Cells.three-tori-finite
fillingsCW = ((C ⊎ C) ⊎ C) , finite≤→isCW Cells.three-circles-finite

seifertCW : (p q r : ℤ) → CW₀
seifertCW p q r = Literal.M p q r , finite≤→isCW
  (pushout-finite≤ (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r)
    2 2 1 Cells.three-tori-finite Cells.core-finite Cells.three-circles-finite)

SeifertLES : (p q r : ℤ) → Type₁
SeifertLES p q r = PushoutLES overlapCW graph×circleCW fillingsCW
  (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) (seifertCW p q r)

abstract
  -- A single invocation for the entire three-torus Seifert span.
  seifert-LES : (p q r : ℤ) → PT.∥ SeifertLES p q r ∥₁
  seifert-LES p q r = finite-pushoutLES-merely overlapCW graph×circleCW fillingsCW
    (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r)
    2 2 1 Cells.three-tori-finite Cells.core-finite Cells.three-circles-finite

  seifert-H-above : (p q r : ℤ) (k : ℕ) → 3 < k → Hzero (seifertCW p q r) k
  seifert-H-above p q r k = finite≤-homology-above (seifertCW p q r) 3 k
    (Cells.seifert-finite p q r)

  seifert-H₄-zero : (p q r : ℤ) → Hzero (seifertCW p q r) 4
  seifert-H₄-zero p q r = seifert-H-above p q r 4 (0 , refl)

  overlap-H₃-zero : Hzero overlapCW 3
  overlap-H₃-zero = finite≤-homology-above overlapCW 2 3 Cells.three-tori-finite (0 , refl)

  fillings-H₂-zero : Hzero fillingsCW 2
  fillings-H₂-zero = finite≤-homology-above fillingsCW 1 2 Cells.three-circles-finite (0 , refl)

  fillings-H₃-zero : Hzero fillingsCW 3
  fillings-H₃-zero = finite≤-homology-above fillingsCW 1 3 Cells.three-circles-finite (1 , refl)

  core-H₃-zero : Hzero graph×circleCW 3
  core-H₃-zero = finite≤-homology-above graph×circleCW 2 3 Cells.core-finite (0 , refl)
