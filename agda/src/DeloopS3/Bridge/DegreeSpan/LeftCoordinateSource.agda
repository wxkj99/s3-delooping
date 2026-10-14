{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LeftCoordinateSource where

-- Actual left H₂ coordinates. The source index is the petal POSITION,
-- reindexed explicitly through SumFin≃Fin; it is never a generator name.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; ¬Fin0 ; toℕ-injective)
import Cubical.Data.SumFin as SF
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠℤAbGroup)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module MarkedProduct ; torus-square-coordinate)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-retraction)
open import DeloopS3.Bridge.CoverChains.Incidence using (Bdy ; RoseEdges ; Dhat)
open import DeloopS3.Cert.Input.Graph.Maps using (Petal)
import DeloopS3.Bridge.CoverChains.Words as Words
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
open Input using (ShortCase)
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
import DeloopS3.Bridge.DegreeSpan.RoseProductProjection as Projection
import DeloopS3.Bridge.DegreeSpan.InitialWordDegrees as Initial
import DeloopS3.Bridge.DegreeSpan.OverlapCoordinates as Overlap
import DeloopS3.Bridge.DegreeSpan.LeftCoordinateAlgebra as Algebra
import DeloopS3.Cert.Check as Ch
open Ch using (Kind)
open import DeloopS3.Bridge.CoverChains.Generators using (targetTorus)
import DeloopS3.Bridge.DegreeSpan.LeftCircleAction as CircleAction
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFromTorus as Circle

-- Neutral index/group adapters are elaborated before any H₂ endpoint.
reindex : {A B : Type₀} → A ≃ B
  → GroupEquiv (AbGroup→Group (ΠℤAbGroup B)) (AbGroup→Group (ΠℤAbGroup A))
reindex {A} {B} e = isoToEquiv i , makeIsGroupHom (λ _ _ → refl)
  where
  i : Iso (B → ℤ) (A → ℤ)
  Iso.fun i f = f ∘ equivFun e
  Iso.inv i g = g ∘ invEq e
  Iso.sec i g = funExt λ a → cong g (retEq e a)
  Iso.ret i f = funExt λ b → cong f (secEq e b)

rank-two : GroupEquiv (AbGroup→Group ℤ[Fin 2 ]) (AbGroup→Group Base.ℤ²)
rank-two = isoToEquiv i , makeIsGroupHom (λ _ _ → refl)
  where
  i : Iso (Fin 2 → ℤ) (ℤ × ℤ)
  Iso.fun i f = f fzero , f (fsuc fzero)
  Iso.inv i (a , b) (zero , p) = a
  Iso.inv i (a , b) (suc zero , p) = b
  Iso.inv i (a , b) (suc (suc k) , p) = Empty.rec p
  Iso.sec i (a , b) = refl
  Iso.ret i f = funExt λ
    { (zero , p) → cong f (toℕ-injective refl)
    ; (suc zero , p) → cong f (toℕ-injective refl)
    ; (suc (suc k) , p) → Empty.rec p }

eLs : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (Pieces.L₀CW c) 2) (AbGroup→Group (RoseEdges c))
eLs c = compGroupEquiv (Pieces.initial-left-H₂ c)
  (reindex (SumFin≃Fin (P.length (Input.gs c))))

source-inclusion : (c : ShortCase) → Bdy c → R.T² → fst (Pieces.O₀CW c)
source-inclusion c b x = Words.faceIndex c b , x

source-component : (c : ShortCase) → Bdy c → R.T² → fst (Pieces.L₀CW c)
source-component c b = R.left (Input.S₀ c) ∘ source-inclusion c b

abstract
  source-projected-agreement : (c : ShortCase) (b : Bdy c) (j : Petal c)
    → Projection.project_e (P.length (Input.gs c)) (Pieces.L₀CW c)
        (Pieces.rose-product-chart (Input.gs c))
        (equivFun (SumFin≃Fin (P.length (Input.gs c))) j)
        ∘ source-component c b
      ≡ Circle.φ (Initial.actualCircleMap c b j)
  source-projected-agreement c b j = funExt λ (u , t) → ΣPathP
    ( cong (λ u → circleToC (Initial.actualProjection c j
        (fst (R.left (Input.S₀ c) (Words.faceIndex c b , u , R.0C)))))
        (sym (circle-retraction u))
    , circle-retraction (snd (source-component c b (u , t)))
        ∙ Initial.source-fibre-is-id c b u t )

  source-component-H₂ : (c : ShortCase) (b : Bdy c) (j : Petal c)
    (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (eLs c))
        (fst (H̃ᶜʷ→ {C = torusCW} {D = Pieces.L₀CW c} 2 (source-component c b)) z) j
      ≡ Words.initialExponent c b j Z.· torus-square-coordinate z
  source-component-H₂ c b j z = CircleAction.projected-component-H₂
    (P.length (Input.gs c)) (Pieces.L₀CW c)
    (Pieces.rose-product-chart (Input.gs c))
    (equivFun (SumFin≃Fin (P.length (Input.gs c))) j)
    (source-component c b) (Initial.actualCircleMap c b j)
    (Words.initialExponent c b j) (source-projected-agreement c b j)
    (Initial.actualCircleMap-degree c b j) z

  source-left-on-component : (c : ShortCase) (b : Bdy c) (j : Petal c)
    (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (eLs c))
        (fst (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.L₀CW c}
          2 (R.left (Input.S₀ c)))
          (fst (H̃ᶜʷ→ {C = torusCW} {D = Pieces.O₀CW c}
            2 (source-inclusion c b)) z)) j
      ≡ Words.initialExponent c b j Z.· torus-square-coordinate z
  source-left-on-component c b j z =
    cong (λ h → equivFun (fst (eLs c)) (fst h z) j)
      (sym (H̃ᶜʷ→comp {C = torusCW} {D = Pieces.O₀CW c} {E = Pieces.L₀CW c}
        2 (R.left (Input.S₀ c)) (source-inclusion c b)))
    ∙ source-component-H₂ c b j z

  source-left-on-summand : (c : ShortCase) (b : Bdy c)
    (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (eLs c))
        (fst (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.L₀CW c}
          2 (R.left (Input.S₀ c))) (fst (Overlap.cover-inclusion₂ c b) z))
      ≡ fst (Dhat c)
          (equivFun (fst (Overlap.coordCover c)) (fst (Overlap.cover-inclusion₂ c b) z))
  source-left-on-summand c b z = funExt (λ j →
    source-left-on-component c b j z
    ∙ sym (Algebra.Dhat-basis-scaled c b (torus-square-coordinate z) j))
    ∙ cong (fst (Dhat c)) (sym (Overlap.cover-inclusion₂-β c b z))

  source-left : (c : ShortCase) (z : fst (H̃ᶜʷ (Pieces.O₀CW c) 2))
    → equivFun (fst (eLs c))
        (fst (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.L₀CW c}
          2 (R.left (Input.S₀ c))) z)
      ≡ fst (Dhat c) (equivFun (fst (Overlap.coordCover c)) z)
  source-left c = Overlap.cover-hom-ext c left right (source-left-on-summand c)
    where
    left right : GroupHom (H̃ᶜʷ (Pieces.O₀CW c) 2) (AbGroup→Group (RoseEdges c))
    left = compGroupHom
      (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.L₀CW c} 2 (R.left (Input.S₀ c)))
      (GroupEquiv→GroupHom (eLs c))
    right = compGroupHom (GroupEquiv→GroupHom (Overlap.coordCover c)) (Dhat c)

