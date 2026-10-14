{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; _+_ ; +-comm)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; ¬Fin0)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.S1.Base using (S¹ ; base)
open import Cubical.HITs.Pushout using
  (cofib ; inl ; inr ; push ; pushoutEquiv ; symPushout)
open import Cubical.HITs.Wedge.Properties using (Iso-⋁genFinSuc-⋁genFin⋁)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.ChainComplex using (∂)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; hasCWskelSphereBouquet/)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (ℤ[]/ImSphereMap ; GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap
  ; inKerGenerator ; genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ ; isGen-genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup using (trivialRelIso)
open import Cubical.Algebra.Group.Subgroup using (imSubgroup ; isNormalIm)
open import Cubical.Algebra.AbGroup using (AbGroup→Group ; AbGroupStr)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤ[Fin_] ; ℤFinGenerator ; agreeOnℤFinGenerator→≡)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.ComponentHomology.Circle
open import DeloopS3.Bridge.ComponentHomology.CircleCofibre using (one-equiv)
open import DeloopS3.Bridge.ComponentHomology.ChainTools
open import DeloopS3.Bridge.ComponentHomology.Finite using (graphCW ; graph-finite)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition using (P ; wedgeLeg)

-- No relators: this is a 1-dimensional skeleton despite being expressed
-- using the library's uniform bouquet-cofibre construction.
no-relators : (n : ℕ) → FinSphereBouquetMap 0 n 0
no-relators n _ = inl tt

private
  empty-cofibre-iso : (n : ℕ) → Iso (cofib (no-relators n)) (SphereBouquet 1 (Fin n))
  Iso.fun (empty-cofibre-iso n) (inl tt) = inl tt
  Iso.fun (empty-cofibre-iso n) (inr x) = x
  Iso.fun (empty-cofibre-iso n) (push (inl tt) i) = inl tt
  Iso.fun (empty-cofibre-iso n) (push (inr ((a , ()) , x)) i)
  Iso.fun (empty-cofibre-iso n) (push (push (a , ()) j) i)
  Iso.inv (empty-cofibre-iso n) = inr
  Iso.sec (empty-cofibre-iso n) x = refl
  Iso.ret (empty-cofibre-iso n) (inl tt) = sym (push (inl tt))
  Iso.ret (empty-cofibre-iso n) (inr x) = refl
  Iso.ret (empty-cofibre-iso n) (push (inl tt) i) j = push (inl tt) (i ∨ ~ j)
  Iso.ret (empty-cofibre-iso n) (push (inr ((a , ()) , x)) i)
  Iso.ret (empty-cofibre-iso n) (push (push (a , ()) j) i)

abstract
  graph-bouquet : SphereBouquet 1 (Fin 2) ≃ P
  graph-bouquet = compEquiv (isoToEquiv Iso-⋁genFinSuc-⋁genFin⋁)
    (compEquiv
      (pushoutEquiv (λ _ → inl tt) (λ _ → base) wedgeLeg wedgeLeg
        (idEquiv Unit) (compEquiv one-equiv S¹≃C) S¹≃C refl refl)
      (symPushout wedgeLeg wedgeLeg))

  graph-cofibre : P ≃ cofib (no-relators 2)
  graph-cofibre = compEquiv (invEquiv graph-bouquet)
    (invEquiv (isoToEquiv (empty-cofibre-iso 2)))

  graph-bouquet-unfold : Path (SphereBouquet 1 (Fin 2) ≃ P) graph-bouquet
    (compEquiv (isoToEquiv Iso-⋁genFinSuc-⋁genFin⋁)
      (compEquiv
        (pushoutEquiv (λ _ → inl tt) (λ _ → base) wedgeLeg wedgeLeg
          (idEquiv Unit) (compEquiv one-equiv S¹≃C) S¹≃C refl refl)
        (symPushout wedgeLeg wedgeLeg)))
  graph-bouquet-unfold = refl

graphSkel : CWskel ℓ-zero
graphSkel = SphereBouquet/ˢᵏᵉˡ (no-relators 2)

graph-skeleton : hasCWskel P
graph-skeleton = graphSkel , compEquiv graph-cofibre
  (snd (hasCWskelSphereBouquet/ (no-relators 2)))

private
  freeGroup : (n : ℕ) → Group₀
  freeGroup n = AbGroup→Group ℤ[Fin n ]

  empty-cokernel : (n : ℕ) → GroupIso (ℤ[]/ImSphereMap (no-relators n)) (freeGroup n)
  empty-cokernel n = invGroupIso (trivialRelIso
    (imSubgroup (bouquetDegree (no-relators n)) ,
      isNormalIm (bouquetDegree (no-relators n))
        (λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin n ]) _ _))
    (λ x y → PT.rec (GroupStr.is-set (snd (freeGroup n)) _ _)
      (λ (_ , p) → GroupTheory.invUniqueL (freeGroup n) (sym p)
        ∙ GroupTheory.invInv (freeGroup n) y)))

abstract
  graph-cells₀ : snd graphSkel .fst 0 ≡ 1
  graph-cells₀ = refl

  graph-cells₁ : snd graphSkel .fst 1 ≡ 2
  graph-cells₁ = refl

  graph-cells₂ : snd graphSkel .fst 2 ≡ 0
  graph-cells₂ = refl

  graph-boundary : ∂ graphSkel 0 ≡ trivGroupHom
  graph-boundary = agreeOnℤFinGenerator→≡ (inKerGenerator (no-relators 2))

  graph-H₁ : GroupEquiv (H̃ᶜʷ graphCW 1) (AbGroup→Group ℤ[Fin 2 ])
  graph-H₁ = compGroupEquiv (chosen-skeleton graphCW graph-skeleton 1)
    (GroupIso→GroupEquiv (compGroupIso
      (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (no-relators 2))
      (empty-cokernel 2)))

  graph-H₀ : Hzero graphCW 0
  graph-H₀ = chosen-zero graphCW graph-skeleton 0
    (one-vertex-homology graphSkel refl)

  graph-H≥2 : (n : ℕ) → Hzero graphCW (2 + n)
  graph-H≥2 n = finite≤-homology-above graphCW 1 (2 + n)
    graph-finite (n , +-comm n 2)

-- Coordinates are ordered (a,b): fzero is the right summand in the
-- library's Fin-suc wedge chart, swapped to d₁ by graph-bouquet.
graph-coordinate : fst (H̃ᶜʷ graphCW 1) → (Fin 2 → ℤ)
graph-coordinate = fst (fst graph-H₁)

graph-generator : Fin 2 → fst (H̃ᶜʷ graphCW 1)
graph-generator k = invEq (fst graph-H₁) (ℤFinGenerator k)

graph-generator-coordinate : (k : Fin 2)
  → graph-coordinate (graph-generator k) ≡ ℤFinGenerator k
graph-generator-coordinate k = secEq (fst graph-H₁) (ℤFinGenerator k)

-- A representative in the actual augmented cellular complex, rather
-- than only an inverse image under an abstract group equivalence.
graph-cell-generator : Fin 2 → fst (H̃ᶜʷ graphCW 1)
graph-cell-generator k = invEq (fst (chosen-skeleton graphCW graph-skeleton 1))
  (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (no-relators 2) k)

abstract
  graph-cell-coordinate : (k : Fin 2)
    → graph-coordinate (graph-cell-generator k) ≡ ℤFinGenerator k
  graph-cell-coordinate k = cong
    (Iso.fun (fst (compGroupIso
      (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (no-relators 2))
      (empty-cokernel 2))))
    (secEq (fst (chosen-skeleton graphCW graph-skeleton 1))
      (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (no-relators 2) k))
    ∙ cong (Iso.fun (fst (empty-cokernel 2)))
      (isGen-genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (no-relators 2) k)

  graph-generator-is-cell : (k : Fin 2) → graph-generator k ≡ graph-cell-generator k
  graph-generator-is-cell k = cong (invEq (fst graph-H₁)) (sym (graph-cell-coordinate k))
    ∙ retEq (fst graph-H₁) (graph-cell-generator k)
