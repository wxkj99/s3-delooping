{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.OuterConsequences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Fin using (isContrFin1)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Cert.Interpret.Short using (octa ; icosa)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.Profile.H1Data.Actual
open import DeloopS3.Bridge.Profile.H1Data.Components
open import DeloopS3.Bridge.Profile.H1Data.Cases using (product-iso ; forget-right)
open import DeloopS3.Bridge.Profile.H1Data.FiniteMaps
open import DeloopS3.Bridge.Profile.H1Data.OuterAlgebra using (C₂ ; C₄)
open import DeloopS3.Bridge.Profile.H1Data.Conjugation

module FromGroups (d : ComponentH1Groups) where
  private
    module D = ComponentH1Groups d
    targetO : GroupEquiv (DirProd (H̃ᶜʷ RCW 1) (H̃ᶜʷ (CCW octa) 1)) V₄
    targetO = GroupIso→GroupEquiv (product-iso (GroupEquiv→GroupIso R-H₁) (GroupEquiv→GroupIso D.target-O))
    targetI : GroupEquiv (DirProd (H̃ᶜʷ RCW 1) (H̃ᶜʷ (CCW icosa) 1)) C₂
    targetI = GroupIso→GroupEquiv (compGroupIso
      (product-iso (GroupEquiv→GroupIso R-H₁) (GroupEquiv→GroupIso D.target-I))
      (forget-right (ℤGroup/ 2) (ℤGroup/ 1) isContrFin1))
    module O = Change (outer-H₁-map octa) D.source-O targetO
    module ICase = Change (outer-H₁-map icosa) D.source-I targetI

  abstract
    outer-O-isEquiv : isEquiv (fst (outer-H₁-map octa))
    outer-O-isEquiv = O.reflect-isEquiv (V₄-onto-isEquiv O.hom (O.onto (outer-H₁-onto octa)))

    outer-I-kernel : GroupEquiv (kerGroup (outer-H₁-map icosa)) C₂
    outer-I-kernel = compGroupEquiv (GroupIso→GroupEquiv ICase.kernel-iso)
      (C₄-onto-kernel ICase.hom (ICase.onto (outer-H₁-onto icosa)))

-- The component-input adapters need no additional p(J), p(R), source-cover
-- marking, or Hurewicz-naturality premise: Actual supplies surjectivity.
abstract
  outer-O-isEquiv-from-inner : ComponentH1Inputs → isEquiv (fst (outer-H₁-map octa))
  outer-O-isEquiv-from-inner d = PT.rec (isPropIsEquiv (fst (outer-H₁-map octa)))
    FromGroups.outer-O-isEquiv (components-from-inner-MV d)

  outer-I-kernel-from-inner : ComponentH1Inputs
    → PT.∥ GroupEquiv (kerGroup (outer-H₁-map icosa)) C₂ ∥₁
  outer-I-kernel-from-inner d = PT.map FromGroups.outer-I-kernel (components-from-inner-MV d)
