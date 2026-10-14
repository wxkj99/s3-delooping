{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.Complex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms hiding (Ker)
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Bridge.CellularPushout.Algebra using (pairHom; fstHom; sndHom)
open import DeloopS3.Bridge.SeifertChains.Block using (module Blocks; module NoIncoming)
import DeloopS3.Bridge.SeifertChains.Matrices as Base
open import DeloopS3.Bridge.CoverChains.OrbitSums
open import DeloopS3.Bridge.CoverChains.Incidence
open import DeloopS3.Bridge.CoverChains.Sums
open import DeloopS3.Bridge.CoverChains.TreeChains using (rootSheet)
import DeloopS3.Cert.Perm as P

private
  module Sum = FiniteSums ℤAbGroup

sumKind : (c : ShortCase) (k : Kind) → (Bd c k → ℤ) → ℤ
sumKind c k = Sum.sumSF

sumKindHom : (c : ShortCase) (k : Kind) (w : Bd c k → ℤ)
  → AbGroupHom (Tori c) ℤAbGroup
fst (sumKindHom c k w) x = sumKind c k (λ b → w b Z.· x (k , b))
snd (sumKindHom c k w) = makeIsGroupHom λ x y →
  cong (sumKind c k) (funExt λ b → Z.·DistR+ (w b) (x (k , b)) (y (k , b)))
  ∙ Sum.sumSF-add (P.length (bdList c k))
      (λ b → w b Z.· x (k , b)) (λ b → w b Z.· y (k , b))

-- Overlap degree zero and the fibre H₁ coordinate are unweighted.
U₀ : (c : ShortCase) → AbGroupHom (Tori c) Base.ℤ³
U₀ c = pairHom {X = Tori c} {Y = ℤAbGroup} {Z = Base.ℤ²} (sumKindHom c A (λ _ → pos 1))
  (pairHom {X = Tori c} {Y = ℤAbGroup} {Z = ℤAbGroup} (sumKindHom c B (λ _ → pos 1)) (sumKindHom c C (λ _ → pos 1)))

-- LocalCharts.overlap-projection has precisely diag(length,1).
-- Its positive degree-two coefficient is length; no sheet factor is
-- inserted in the fibre H₁ coordinate.
U₂ : (c : ShortCase) → AbGroupHom (Tori c) Base.ℤ³
U₂ c = pairHom {X = Tori c} {Y = ℤAbGroup} {Z = Base.ℤ²} (sumKindHom c A (λ b → pos (suc (ellPred c A b))))
  (pairHom {X = Tori c} {Y = ℤAbGroup} {Z = ℤAbGroup} (sumKindHom c B (λ b → pos (suc (ellPred c B b))))
           (sumKindHom c C (λ b → pos (suc (ellPred c C b)))))

sumBoundary : (c : ShortCase) → AbGroupHom (Tori c) ℤAbGroup
sumBoundary c = compGroupHom (U₀ c) Base.sum₃

Overlap₁ : ShortCase → AbGroup ℓ-zero
Overlap₁ c = dirProdAb (Tori c) (Tori c)

rightRows : (c : ShortCase) → AbGroupHom (Overlap₁ c) (Tori c)
fst (rightRows c) (u , h) (k , b) = localWeight c k Z.· u (k , b)
  Z.+ pos (suc (orderPred c k b)) Z.· h (k , b)
snd (rightRows c) = makeIsGroupHom λ (u , h) (v , t) → funExt λ (k , b) →
  cong₂ Z._+_ (Z.·DistR+ (localWeight c k) (u (k , b)) (v (k , b)))
    (Z.·DistR+ (pos (suc (orderPred c k b))) (h (k , b)) (t (k , b)))
  ∙ AbGroupTheory.comm-4 ℤAbGroup
      (localWeight c k Z.· u (k , b)) (localWeight c k Z.· v (k , b))
      (pos (suc (orderPred c k b)) Z.· h (k , b))
      (pos (suc (orderPred c k b)) Z.· t (k , b))

CoverVertex₁ : ShortCase → AbGroup ℓ-zero
CoverVertex₁ c = dirProdAb (RoseEdges c) (dirProdAb ℤAbGroup (Tori c))

Ahat : (c : ShortCase) → AbGroupHom (Overlap₁ c) (CoverVertex₁ c)
Ahat c = pairHom {X = Overlap₁ c} {Y = RoseEdges c} {Z = dirProdAb ℤAbGroup (Tori c)} (compGroupHom (fstHom (Tori c) (Tori c)) (Dhat c))
  (pairHom {X = Overlap₁ c} {Y = ℤAbGroup} {Z = Tori c} (compGroupHom (sndHom (Tori c) (Tori c)) (sumBoundary c))
    (negGroupHom (Overlap₁ c) (Tori c) (rightRows c)))

module Cover (c : ShortCase) = Blocks ℤAbGroup (RoseEdges c) (Tori c)
  (Overlap₁ c) (sumBoundary c) (Dhat c) (Ahat c)

-- Tree-contracted graph × circle, orbit tori, and orbit core circles.
-- Ordinary ranks are (6,15,14,5,0) / (13,36,35,12,0).
-- The ordinary degree-three generators are ALL overlap-torus prisms.
Kcov : ShortCase → ChainComplex ℓ-zero
Kcov c = Cover.K c

cover-ones-cycle : (c : ShortCase) → fst (ker∂n 3 (Kcov c))
cover-ones-cycle c = ones c , ΣPathP (ones-cycle c , refl)

cover-ones-class : (c : ShortCase) → fst (homology 3 (Kcov c))
cover-ones-class c = SQ.[ cover-ones-cycle c ]

private
  module Top (c : ShortCase) = NoIncoming (Kcov c) 3 (λ _ → refl)

abstract
  cover-H₃-chain : (c : ShortCase) → GroupEquiv (homology 3 (Kcov c)) ℤGroup
  cover-H₃-chain c = compGroupEquiv (Top.H-to-cycle c)
    (compGroupEquiv (Cover.top-cycles c) (cover-kernel c))

  cover-H₃-ones-coordinate : (c : ShortCase)
    → equivFun (fst (cover-H₃-chain c)) (cover-ones-class c) ≡ pos 1
  cover-H₃-ones-coordinate c =
    cong (λ z → equivFun (fst (cover-kernel c)) (equivFun (fst (Cover.top-cycles c)) z))
      (Top.H-to-cycle-class c (cover-ones-cycle c))
    ∙ cong (λ x → sheetValue c x A (rootSheet c))
        (Cover.top-cycles-coordinate c (cover-ones-cycle c))

  cover-H₃-ones : (c : ShortCase)
    → invEq (fst (cover-H₃-chain c)) (pos 1) ≡ cover-ones-class c
  cover-H₃-ones c = cong (invEq (fst (cover-H₃-chain c))) (sym (cover-H₃-ones-coordinate c))
    ∙ retEq (fst (cover-H₃-chain c)) (cover-ones-class c)

F₃ : (c : ShortCase) → fst (Tori c) → fst Base.ℤ³
F₃ c = fst (U₂ c)

N-times-target-ones : (c : ShortCase) → fst Base.ℤ³
N-times-target-ones c = pos (N c) , pos (N c) , pos (N c)

abstract
  F₃-ones : (c : ShortCase) → F₃ c (ones c) ≡ N-times-target-ones c
  F₃-ones octa = refl
  F₃-ones icosa = refl
