{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.InnerH2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.DMCExactness.Groups using
  (exact-composite ; exact-zero-map-middle ; equiv-kernel-zero)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.H1Data.Coordinates
open import DeloopS3.Bridge.Profile.H1Data.Inner
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

abstract
  onto-mono-middle-zero : {A B M S V : Group₀}
    (s : GroupHom A B) (v : GroupHom B M) (d : GroupHom M S) (t : GroupHom S V)
    → Exact₃ s v → Exact₃ v d → Exact₃ d t
    → isSurjective s → isInjective t → isContr (fst M)
  onto-mono-middle-zero s v d t ex₀ ex₁ ex₂ onto mono = exact-zero-map-middle v d ex₁
    (λ b → invEq (ex₀ b) (onto b))
    (λ m → mono (fst d m) (exact-composite {u = d} {v = t} ex₂ m))

module ForInner (q n : ℤ) where
  private
    module S = Literal.Seifert (pos 2) q n
  open Inner q n

  -- The left H₂ boundary D is onto and the right H₂ map is zero.
  -- Only their combined surjectivity is required.
  H2SourceOnto : Type₀
  H2SourceOnto = (v : fst (DirProd (H̃ᶜʷ leftCW 2) (H̃ᶜʷ rightCW 2)))
    → PT.∥ fiber (actual-source overlapCW leftCW rightCW S.allLeft S.allRight 2) v ∥₁

  abstract
    H₂-from-inner-MV : H1Coordinates → isInjective (Araw (pos 2) q n)
      → H2SourceOnto → Hzero totalCW 2
    H₂-from-inner-MV dataH raw-mono top-onto = PT.rec isPropIsContr build inner-LES
      where
      module Data = H1CoordinateData dataH
      build : GeometricPushoutLES overlapCW leftCW rightCW S.allLeft S.allRight totalCW
        → Hzero totalCW 2
      build les = onto-mono-middle-zero (Seq.source-map 2) (Seq.sum-map 2) (Seq.boundary 1) (Seq.source-map 1)
        (Seq.exact-target 2 (2 , refl)) (Seq.exact-total 1 (3 , refl)) (Seq.exact-source 1 (3 , refl))
        (λ v → PT.map (λ { (a , p) → a , Seq.source-agrees 2 a ∙ p }) (top-onto v)) mono
        where
        module Seq = SpanSequenceData (snd les)
        mono : isInjective (Seq.source-map 1)
        mono a p = equiv-kernel-zero (GroupEquiv→GroupHom Data.overlap-coordinates)
          (snd (fst Data.overlap-coordinates)) a
          (raw-mono (equivFun (fst Data.overlap-coordinates) a)
            (Data.matrix-square a
              ∙ cong (equivFun (fst Data.vertices)) (sym (Seq.source-agrees 1 a) ∙ p)
              ∙ IsGroupHom.pres1 (snd Data.vertices)))
