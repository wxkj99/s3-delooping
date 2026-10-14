{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.OverlapCoordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Cubical.Data.Bool using (if_then_else_)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
import Cubical.Data.SumFin as SF
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (torus-skeleton)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using (torus-H₂ ; torus-square-coordinate)
open import DeloopS3.Bridge.SpanCells using (torus-finite)
open import DeloopS3.Bridge.CoverChains.OrbitSums
open import DeloopS3.Bridge.CoverChains.Incidence using (Bdy ; Tori)
open import DeloopS3.Bridge.CoverChains.Words using (faceIndex ; basis)
open import DeloopS3.Bridge.CoverChains.Complex using (U₂ ; sumKind)
open import DeloopS3.Bridge.CoverChains.Generators using (targetTorus ; F₃-basis)
open import DeloopS3.Bridge.CoverChains.Sums using (module FiniteSums)
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
open import DeloopS3.Bridge.DegreeSpan.FiniteCoproductGroups
import DeloopS3.Bridge.DegreeSpan.FiniteCoproductCoordinates as Finite
open import DeloopS3.Bridge.DegreeSpan.TorusIntegerH2 using (torus-multiplier-H₂)
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)
import DeloopS3.Cert.Input.LocalCharts as Local
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch

module V = Vectors ℤAbGroup
module Sum = FiniteSums ℤAbGroup
module T = Finite.Coordinates torusCW torus-skeleton torus-finite 1 (2 , refl) ℤAbGroup torus-H₂

face-count : ShortCase → ℕ
face-count c = P.length (Ch.faces (S₀ c))

-- This is allBoundaryIndex itself, not an enumeration guessed from a rank.
coordCover : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (Pieces.O₀CW c) 2) (AbGroup→Group (Tori c))
coordCover c = compGroupEquiv
  (T.coord (face-count c) (Pieces.O₀CW c) (idEquiv _))
  (V.reindex (allBoundaryIndex c))

private
  kind-index : Kind → SF.Fin 3
  kind-index A = SF.fzero
  kind-index B = SF.fsuc SF.fzero
  kind-index C = SF.fsuc (SF.fsuc SF.fzero)

  base-iso : Iso (Kind × R.T²) (SF.Fin 3 × R.T²)
  Iso.fun base-iso (k , x) = kind-index k , x
  Iso.inv base-iso (SF.fzero , x) = A , x
  Iso.inv base-iso (SF.fsuc SF.fzero , x) = B , x
  Iso.inv base-iso (SF.fsuc (SF.fsuc SF.fzero) , x) = C , x
  Iso.inv base-iso (SF.fsuc (SF.fsuc (SF.fsuc ())) , x)
  Iso.sec base-iso (SF.fzero , x) = refl
  Iso.sec base-iso (SF.fsuc SF.fzero , x) = refl
  Iso.sec base-iso (SF.fsuc (SF.fsuc SF.fzero) , x) = refl
  Iso.sec base-iso (SF.fsuc (SF.fsuc (SF.fsuc ())) , x)
  Iso.ret base-iso (A , x) = refl
  Iso.ret base-iso (B , x) = refl
  Iso.ret base-iso (C , x) = refl

  triple-iso : GroupIso (V.V 3) (AbGroup→Group Base.ℤ³)
  Iso.fun (fst triple-iso) v = v SF.fzero , v (SF.fsuc SF.fzero) , v (SF.fsuc (SF.fsuc SF.fzero))
  Iso.inv (fst triple-iso) (a , b , c) SF.fzero = a
  Iso.inv (fst triple-iso) (a , b , c) (SF.fsuc SF.fzero) = b
  Iso.inv (fst triple-iso) (a , b , c) (SF.fsuc (SF.fsuc SF.fzero)) = c
  Iso.inv (fst triple-iso) (a , b , c) (SF.fsuc (SF.fsuc (SF.fsuc ())))
  Iso.sec (fst triple-iso) _ = refl
  Iso.ret (fst triple-iso) v = funExt λ
    { SF.fzero → refl ; (SF.fsuc SF.fzero) → refl
    ; (SF.fsuc (SF.fsuc SF.fzero)) → refl ; (SF.fsuc (SF.fsuc (SF.fsuc ()))) }
  snd triple-iso = makeIsGroupHom λ _ _ → refl

coordBase : (c : ShortCase)
  → GroupEquiv (H̃ᶜʷ (Pieces.OᵦCW c) 2) (AbGroup→Group Base.ℤ³)
coordBase c = compGroupEquiv
  (T.coord 3 (Pieces.OᵦCW c) (isoToEquiv base-iso))
  (GroupIso→GroupEquiv triple-iso)

cover-inclusion : (c : ShortCase) → Bdy c → R.T² → R.O (S₀ c)
cover-inclusion c b x = faceIndex c b , x

base-inclusion : (c : ShortCase) → Kind → R.T² → fst (Pieces.OᵦCW c)
base-inclusion c k x = k , x

cover-inclusion₂ : (c : ShortCase) (b : Bdy c)
  → GroupHom (H̃ᶜʷ torusCW 2) (H̃ᶜʷ (Pieces.O₀CW c) 2)
cover-inclusion₂ c b = H̃ᶜʷ→ {C = torusCW} {D = Pieces.O₀CW c} 2 (cover-inclusion c b)

base-inclusion₂ : (c : ShortCase) (k : Kind)
  → GroupHom (H̃ᶜʷ torusCW 2) (H̃ᶜʷ (Pieces.OᵦCW c) 2)
base-inclusion₂ c k = H̃ᶜʷ→ {C = torusCW} {D = Pieces.OᵦCW c} 2 (base-inclusion c k)

private
  abstract
    point-scaled : {n : ℕ} (i j : SF.Fin n) (a : ℤ)
      → V.point i a j ≡ (if SF.toℕ i ≡ᵇ SF.toℕ j then pos 1 else pos 0) Z.· a
    point-scaled {suc n} SF.fzero SF.fzero a = sym (Z.·IdL a)
    point-scaled {suc n} SF.fzero (SF.fsuc j) a = sym (Z.·AnnihilL a)
    point-scaled {suc n} (SF.fsuc i) SF.fzero a = sym (Z.·AnnihilL a)
    point-scaled {suc n} (SF.fsuc i) (SF.fsuc j) a = point-scaled i j a

abstract
  cover-inclusion₂-β : (c : ShortCase) (b : Bdy c) (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (coordCover c)) (fst (cover-inclusion₂ c b) z)
      ≡ (λ b′ → basis c b b′ Z.· torus-square-coordinate z)
  cover-inclusion₂-β c b z =
    cong (λ v → v ∘ faceIndex c)
      (T.inclusion-β (face-count c) (Pieces.O₀CW c) (idEquiv _) (faceIndex c b) z)
    ∙ funExt λ b′ → point-scaled (faceIndex c b) (faceIndex c b′) (torus-square-coordinate z)

  base-inclusion₂-β : (c : ShortCase) (k : Kind) (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (coordBase c)) (fst (base-inclusion₂ c k) z)
      ≡ targetTorus k (torus-square-coordinate z)
  base-inclusion₂-β c A z = cong (Iso.fun (fst triple-iso))
    (T.inclusion-β 3 (Pieces.OᵦCW c) (isoToEquiv base-iso) SF.fzero z)
  base-inclusion₂-β c B z = cong (Iso.fun (fst triple-iso))
    (T.inclusion-β 3 (Pieces.OᵦCW c) (isoToEquiv base-iso) (SF.fsuc SF.fzero) z)
  base-inclusion₂-β c C z = cong (Iso.fun (fst triple-iso))
    (T.inclusion-β 3 (Pieces.OᵦCW c) (isoToEquiv base-iso) (SF.fsuc (SF.fsuc SF.fzero)) z)

-- Assembly.initial-span reuses Local.local-charts. Thus the first step
-- below is the projection equation of Map.πO itself.
abstract
  overlap-projection : (c : ShortCase) (b : Bdy c) (x : R.T²)
    → Map.πO c (cover-inclusion c b x)
      ≡ base-inclusion c (fst b)
          (TorusMultiplier.actual (pos (suc (ellPred c (fst b) (snd b)))) x)
  overlap-projection c b (u , t) =
    Local.LocalCharts.overlap-projection (Local.local-charts c) (faceIndex c b) u t
    ∙ (λ i → Local.kind-index fd (~ i) ,
        R.mulC (pos (Local.length-index fd (~ i))) u , t)
    ∙ cong (λ q → fst q , R.mulC (pos (suc (ellPred c (fst q) (snd q)))) u , t)
        (retEq (allBoundaryIndex c) b)
    where
    fd : Local.FaceData c (faceIndex c b)
    fd = Local.face-data c (faceIndex c b)

private
  scale₃ : fst Base.ℤ³ → ℤ → fst Base.ℤ³
  scale₃ (a , b , c) t = a Z.· t , b Z.· t , c Z.· t

  abstract
    sum-scale : (n : ℕ) (f : SF.Fin n → ℤ) (a : ℤ)
      → Sum.sumSF (λ i → f i Z.· a) ≡ Sum.sumSF f Z.· a
    sum-scale zero f a = sym (Z.·AnnihilL a)
    sum-scale (suc n) f a = cong (f SF.fzero Z.· a Z.+_)
      (sum-scale n (f ∘ SF.fsuc) a)
      ∙ sym (Z.·DistL+ (f SF.fzero) (Sum.sumSF (f ∘ SF.fsuc)) a)

    weighted-scale : (c : ShortCase) (k : Kind) (w : Bd c k → ℤ)
      (v : fst (Tori c)) (a : ℤ)
      → sumKind c k (λ b → w b Z.· (v (k , b) Z.· a))
        ≡ sumKind c k (λ b → w b Z.· v (k , b)) Z.· a
    weighted-scale c k w v a = cong (sumKind c k)
      (funExt λ b → Z.·Assoc (w b) (v (k , b)) a)
      ∙ sum-scale (P.length (bdList c k)) (λ b → w b Z.· v (k , b)) a

    U₂-scale : (c : ShortCase) (v : fst (Tori c)) (a : ℤ)
      → fst (U₂ c) (λ b → v b Z.· a) ≡ scale₃ (fst (U₂ c) v) a
    U₂-scale c v a = ΣPathP
      (weighted-scale c A (λ b → pos (suc (ellPred c A b))) v a , ΣPathP
        (weighted-scale c B (λ b → pos (suc (ellPred c B b))) v a ,
         weighted-scale c C (λ b → pos (suc (ellPred c C b))) v a))

    target-scale : (k : Kind) (t a : ℤ)
      → scale₃ (targetTorus k t) a ≡ targetTorus k (t Z.· a)
    target-scale A t a = ΣPathP (refl , ΣPathP (Z.·AnnihilL a , Z.·AnnihilL a))
    target-scale B t a = ΣPathP (Z.·AnnihilL a , ΣPathP (refl , Z.·AnnihilL a))
    target-scale C t a = ΣPathP (Z.·AnnihilL a , ΣPathP (Z.·AnnihilL a , refl))

abstract
  U₂-basis-scaled : (c : ShortCase) (b : Bdy c) (a : ℤ)
    → fst (U₂ c) (λ b′ → basis c b b′ Z.· a)
      ≡ targetTorus (fst b) (pos (suc (ellPred c (fst b) (snd b))) Z.· a)
  U₂-basis-scaled c (k , b) a = U₂-scale c (basis c (k , b)) a
    ∙ cong (λ v → scale₃ v a) (F₃-basis c k b)
    ∙ target-scale k (pos (suc (ellPred c k b))) a

-- Both H̃ᶜʷ→comp steps have the actual endpoint witnesses. The middle
-- equality is exactly overlap-projection, not an unrelated torus diagram.
abstract
  overlap₂-on-summand : (c : ShortCase) (b : Bdy c) (z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst (coordBase c))
        (fst (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c))
          (fst (cover-inclusion₂ c b) z))
      ≡ fst (U₂ c) (equivFun (fst (coordCover c)) (fst (cover-inclusion₂ c b) z))
  overlap₂-on-summand c b z =
    cong (equivFun (fst (coordBase c))) (cong (λ h → fst h z)
      (sym (H̃ᶜʷ→comp {C = torusCW} {D = Pieces.O₀CW c} {E = Pieces.OᵦCW c} 2
        (Map.πO c) (cover-inclusion c b))
      ∙ cong (H̃ᶜʷ→ {C = torusCW} {D = Pieces.OᵦCW c} 2)
          (funExt (overlap-projection c b))
      ∙ H̃ᶜʷ→comp {C = torusCW} {D = torusCW} {E = Pieces.OᵦCW c} 2
          (base-inclusion c (fst b)) (TorusMultiplier.actual ℓ)))
    ∙ base-inclusion₂-β c (fst b)
        (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 (TorusMultiplier.actual ℓ)) z)
    ∙ cong (targetTorus (fst b)) (torus-multiplier-H₂ ℓ z)
    ∙ sym (U₂-basis-scaled c b (torus-square-coordinate z))
    ∙ cong (fst (U₂ c)) (sym (cover-inclusion₂-β c b z))
    where
    ℓ : ℤ
    ℓ = pos (suc (ellPred c (fst b) (snd b)))

-- Unconditional, on every class, with the exact two public coordinates.
abstract
  overlap₂ : (c : ShortCase) (z : fst (H̃ᶜʷ (Pieces.O₀CW c) 2))
    → equivFun (fst (coordBase c))
        (fst (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c)) z)
      ≡ fst (U₂ c) (equivFun (fst (coordCover c)) z)
  overlap₂ c = T.hom-ext (face-count c) (Pieces.O₀CW c) (idEquiv _) left right on-face
    where
    left right : GroupHom (H̃ᶜʷ (Pieces.O₀CW c) 2) (AbGroup→Group Base.ℤ³)
    left = compGroupHom
      (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c))
      (GroupEquiv→GroupHom (coordBase c))
    right = compGroupHom (GroupEquiv→GroupHom (coordCover c)) (U₂ c)

    face-class : R.FaceIx (S₀ c) → fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ (Pieces.O₀CW c) 2)
    face-class i z = fst (H̃ᶜʷ→ {C = torusCW} {D = Pieces.O₀CW c} 2 (λ x → i , x)) z

    on-face : (i : R.FaceIx (S₀ c)) (z : fst (H̃ᶜʷ torusCW 2))
      → fst left (face-class i z) ≡ fst right (face-class i z)
    on-face i z = subst (λ j → fst left (face-class j z) ≡ fst right (face-class j z))
      (secEq (allBoundaryIndex c) i)
      (overlap₂-on-summand c (invEq (allBoundaryIndex c) i) z)

-- Reusable by both left-map adapters: testing all actual torus summands
-- suffices, with no separately chosen coordinates or generator premise.
abstract
  cover-hom-ext : (c : ShortCase) {G : Group₀}
    (f g : GroupHom (H̃ᶜʷ (Pieces.O₀CW c) 2) G)
    → ((b : Bdy c) (z : fst (H̃ᶜʷ torusCW 2))
      → fst f (fst (cover-inclusion₂ c b) z) ≡ fst g (fst (cover-inclusion₂ c b) z))
    → (z : fst (H̃ᶜʷ (Pieces.O₀CW c) 2)) → fst f z ≡ fst g z
  cover-hom-ext c f g p = T.hom-ext (face-count c) (Pieces.O₀CW c) (idEquiv _) f g
    (λ i z → subst
      (λ j → fst f (face-class j z) ≡ fst g (face-class j z))
      (secEq (allBoundaryIndex c) i) (p (invEq (allBoundaryIndex c) i) z))
    where
    face-class : R.FaceIx (S₀ c) → fst (H̃ᶜʷ torusCW 2) → fst (H̃ᶜʷ (Pieces.O₀CW c) 2)
    face-class i z = fst (H̃ᶜʷ→ {C = torusCW} {D = Pieces.O₀CW c} 2 (λ x → i , x)) z

  base-hom-ext : (c : ShortCase) {G : Group₀}
    (f g : GroupHom (H̃ᶜʷ (Pieces.OᵦCW c) 2) G)
    → ((k : Kind) (z : fst (H̃ᶜʷ torusCW 2))
      → fst f (fst (base-inclusion₂ c k) z) ≡ fst g (fst (base-inclusion₂ c k) z))
    → (z : fst (H̃ᶜʷ (Pieces.OᵦCW c) 2)) → fst f z ≡ fst g z
  base-hom-ext c f g p = T.hom-ext 3 (Pieces.OᵦCW c) (isoToEquiv base-iso) f g
    λ { SF.fzero z → p A z
      ; (SF.fsuc SF.fzero) z → p B z
      ; (SF.fsuc (SF.fsuc SF.fzero)) z → p C z
      ; (SF.fsuc (SF.fsuc (SF.fsuc ()))) z }
