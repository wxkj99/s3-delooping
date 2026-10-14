{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Inner where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.HITs.Pushout.Base using (Pushout)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.FiniteDim using (pushout-finite≤)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging using (finite-pushoutLES-merely)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.H1Data.Cokernel
open import DeloopS3.Bridge.Profile.H1Data.MV
open import DeloopS3.Bridge.Profile.H1Data.Coordinates
open import DeloopS3.Move.CancelMinimal using (C ; T²)
import DeloopS3.Bridge.SpanCells as Cells
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

module Inner (q n : ℤ) where
  private
    module S = Literal.Seifert (pos 2) q n

  overlapCW leftCW rightCW totalCW : CW₀
  overlapCW = ((T² ⊎ T²) ⊎ T²) , finite≤→isCW Cells.three-tori-finite
  leftCW = Literal.Core , finite≤→isCW Cells.core-finite
  rightCW = ((C ⊎ C) ⊎ C) , finite≤→isCW Cells.three-circles-finite
  totalCW = Literal.M (pos 2) q n , finite≤→isCW
    (pushout-finite≤ S.allLeft S.allRight 2 2 1
      Cells.three-tori-finite Cells.core-finite Cells.three-circles-finite)

  -- Coordinates for the actual inner-span maps, including their matrix square
  -- and the injective H₀ tail for the disconnected overlap.
  H1Coordinates : Type₀
  H1Coordinates = H1CoordinateData (H̃ᶜʷ overlapCW 1)
    (DirProd (H̃ᶜʷ leftCW 1) (H̃ᶜʷ rightCW 1)) (H̃ᶜʷ overlapCW 0)
    (DirProd (H̃ᶜʷ leftCW 0) (H̃ᶜʷ rightCW 0))
    (actual-source overlapCW leftCW rightCW S.allLeft S.allRight 1)
    (actual-source overlapCW leftCW rightCW S.allLeft S.allRight 0) q n

  abstract
    inner-LES : PT.∥ GeometricPushoutLES overlapCW leftCW rightCW S.allLeft S.allRight totalCW ∥₁
    inner-LES = finite-pushoutLES-merely overlapCW leftCW rightCW S.allLeft S.allRight
      2 2 1 Cells.three-tori-finite Cells.core-finite Cells.three-circles-finite

    H₁-from-inner-MV : H1Coordinates
      → PT.∥ GroupEquiv (H̃ᶜʷ totalCW 1) (Coker (Araw (pos 2) q n)) ∥₁
    H₁-from-inner-MV dataH = PT.map build inner-LES
      where
      module Data = H1CoordinateData dataH
      build : GeometricPushoutLES overlapCW leftCW rightCW S.allLeft S.allRight totalCW
        → GroupEquiv (H̃ᶜʷ totalCW 1) (Coker (Araw (pos 2) q n))
      build les = geometric-H₁-cokernel overlapCW leftCW rightCW totalCW S.allLeft S.allRight les q n
        Data.overlap-coordinates Data.vertices
        (λ a → Data.matrix-square a ∙ cong (equivFun (fst Data.vertices)) (sym (Seq.source-agrees 1 a)))
        (λ a p → Data.zero-tail a (sym (Seq.source-agrees 0 a) ∙ p))
        where
        module Seq = SpanSequenceData (snd les)
