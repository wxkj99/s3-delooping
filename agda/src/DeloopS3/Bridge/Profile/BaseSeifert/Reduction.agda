{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Reduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group ; AbGroupStr)
open import Cubical.Algebra.ChainComplex.Homology using (homology)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim using (Hzero)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.SeifertChains.Seifert
open import DeloopS3.Bridge.Profile.BaseSeifert.Groups
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates
open import DeloopS3.Bridge.Profile.BaseSeifert.Sequence
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

seifert-source : (p q r : ℤ) (n : ℕ)
  → GroupHom (H̃ᶜʷ overlapCW (suc n))
    (DirProd (H̃ᶜʷ graph×circleCW (suc n)) (H̃ᶜʷ fillingsCW (suc n)))
seifert-source p q r n = signed-hom overlapCW graph×circleCW fillingsCW n
  (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r)

-- Map comparison types with fixed actual CW endpoints and
-- the positive-degree coproduct coordinates.
DegreeTwoComparison : (p q r : ℤ) → Type
DegreeTwoComparison p q r = (z : fst (H̃ᶜʷ overlapCW 2)) →
  equivFun (fst vertices-H₂)
    (actual-source overlapCW graph×circleCW fillingsCW
      (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 2 z)
  ≡ fst D (equivFun (fst overlap-H₂) z)

DegreeOneComparison : (p q r : ℤ) → Type
DegreeOneComparison p q r = (z : fst (H̃ᶜʷ overlapCW 1)) →
  equivFun (fst vertices-H₁)
    (actual-source overlapCW graph×circleCW fillingsCW
      (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 1 z)
  ≡ fst (Araw p q r) (equivFun (fst overlap-H₁) z)

module FromLES (p q r : ℤ) (witness : SeifertLES p q r) where
  private
    f = Literal.Seifert.allLeft p q r
    g = Literal.Seifert.allRight p q r
  module L = SpanSequenceData (snd witness)
  module Q = Canonical (H̃ᶜʷ overlapCW) (H̃ᶜʷ graph×circleCW) (H̃ᶜʷ fillingsCW)
    (H̃ᶜʷ (seifertCW p q r)) (actual-source overlapCW graph×circleCW fillingsCW f g)
    (actual-sum overlapCW graph×circleCW fillingsCW f g (seifertCW p q r) (fst witness))
    (snd witness) (seifert-source p q r 1) (seifert-source p q r 0)
    (signed-hom-eval overlapCW graph×circleCW fillingsCW 1 f g)
    (signed-hom-eval overlapCW graph×circleCW fillingsCW 0 f g)
  module Top = Q.Top core-H₃-zero fillings-H₃-zero

abstract
  -- Unconditional ACTUAL homology, with the ACTUAL signed-source kernel.
  -- No D/chain-model comparison hypothesis is used here.
  seifert-H₃-kernel : (p q r : ℤ)
    → PT.∥ GroupEquiv (H̃ᶜʷ (seifertCW p q r) 3) (kerGroup (seifert-source p q r 1)) ∥₁
  seifert-H₃-kernel p q r = PT.map
    (λ witness → FromLES.Top.kernel-equiv p q r witness) (seifert-LES p q r)

module WithDegreeTwo (p q r : ℤ) (degree-two : DegreeTwoComparison p q r) where
  private
    f = Literal.Seifert.allLeft p q r
    g = Literal.Seifert.allRight p q r
    module MC = MatrixConsequences (H̃ᶜʷ overlapCW) (H̃ᶜʷ graph×circleCW) (H̃ᶜʷ fillingsCW)
      (H̃ᶜʷ (seifertCW p q r)) (actual-source overlapCW graph×circleCW fillingsCW f g)
      (seifert-source p q r 1) (seifert-source p q r 0)
      (signed-hom-eval overlapCW graph×circleCW fillingsCW 1 f g)
      (signed-hom-eval overlapCW graph×circleCW fillingsCW 0 f g)
      overlap-H₂ vertices-H₂ overlap-H₁ vertices-H₁ core-H₃-zero fillings-H₃-zero degree-two

    module At (witness : SeifertLES p q r) = MC.ForSequence
      (actual-sum overlapCW graph×circleCW fillingsCW f g (seifertCW p q r) (fst witness))
      (snd witness)

  MarkedTop : Type₁
  MarkedTop = Σ[ witness ∈ SeifertLES p q r ] At.Marked witness

  abstract
    marked-H₃ : PT.∥ MarkedTop ∥₁
    marked-H₃ = PT.map {A = SeifertLES p q r} {B = MarkedTop}
      (λ witness → witness , At.marked witness) (seifert-LES p q r)

    H₃-integers : PT.∥ GroupEquiv (H̃ᶜʷ (seifertCW p q r) 3) ℤGroup ∥₁
    H₃-integers = PT.map {A = MarkedTop}
      {B = GroupEquiv (H̃ᶜʷ (seifertCW p q r) 3) ℤGroup}
      (λ w → fst (snd w)) marked-H₃

    H₂-from-degree-one : DegreeOneComparison p q r
      → ((a : fst ℤ⁶) → fst (Araw p q r) a ≡ AbGroupStr.0g (snd vertex₁)
          → a ≡ AbGroupStr.0g (snd ℤ⁶))
      → Hzero (seifertCW p q r) 2
    H₂-from-degree-one degree-one kill = PT.rec
      {A = SeifertLES p q r} {P = Hzero (seifertCW p q r) 2} isPropIsContr
      (λ witness → At.H₂-zero witness p q r degree-one kill) (seifert-LES p q r)
  -- The degree-two comparison identifies actual homology with the all-ones class,
  -- marked by the same MV boundary; this is not a cellular-chain equivalence.
  module Marked (w : MarkedTop) where
    integer-equiv : GroupEquiv (H̃ᶜʷ (seifertCW p q r) 3) ℤGroup
    integer-equiv = fst (snd w)

    generator : fst (H̃ᶜʷ (seifertCW p q r) 3)
    generator = invEq (fst integer-equiv) (pos 1)

    generator-boundary : equivFun (fst overlap-H₂)
      (fst (SpanSequenceData.boundary (snd (fst w)) 2) generator)
      ≡ (pos 1 , pos 1 , pos 1)
    generator-boundary = snd (snd w) (pos 1)

    generator-boundary-is-ones :
      fst (SpanSequenceData.boundary (snd (fst w)) 2) generator ≡ overlap-ones
    generator-boundary-is-ones =
      sym (retEq (fst overlap-H₂) (fst (SpanSequenceData.boundary (snd (fst w)) 2) generator))
      ∙ cong (invEq (fst overlap-H₂)) (generator-boundary ∙ sym overlap-ones-coordinate)
      ∙ retEq (fst overlap-H₂) overlap-ones

    chain-comparison : GroupEquiv (H̃ᶜʷ (seifertCW p q r) 3) (homology 3 (seifertK p q r))
    chain-comparison = compGroupEquiv integer-equiv (invGroupEquiv (seifert-H₃ p q r))

    generator-is-ones : equivFun (fst chain-comparison) generator ≡ seifert-ones-class p q r
    generator-is-ones = cong (invEq (fst (seifert-H₃ p q r))) (secEq (fst integer-equiv) (pos 1))
      ∙ seifert-H₃-ones p q r
