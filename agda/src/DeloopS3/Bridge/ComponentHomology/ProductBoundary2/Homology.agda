{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; isContrFin1)
open import Cubical.Data.Sigma using (_×_)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_] ; ℤFinGenerator)
open import Cubical.CW.Base using (hasCWskel ; realise)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; CW-AugChainComplex)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
open import DeloopS3.Bridge.ComponentHomology.ChainTools
open import DeloopS3.Bridge.ComponentHomology.ZeroDifferentials
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW ; torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Cellular

open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Groups public

module GraphProduct = MarkedProduct 2 graph×circleCW (snd graph×circle-skeleton)
module TorusProduct = MarkedProduct 1 torusCW (snd torus-skeleton)

-- The target wedge chart puts h first, followed by the rose edges.
-- The source chart labels the cellular square generators by a×h, b×h;
-- these markings are defined without a homological cross product.
graph×circle-H₁ : GroupEquiv (H̃ᶜʷ graph×circleCW 1) (AbGroup→Group ℤ[Fin 3 ])
graph×circle-H₁ = GraphProduct.H₁

graph×circle-H₂ : GroupEquiv (H̃ᶜʷ graph×circleCW 2) (AbGroup→Group ℤ[Fin 2 ])
graph×circle-H₂ = GraphProduct.H₂

graph×circle-H₃ : Hzero graph×circleCW 3
graph×circle-H₃ = GraphProduct.H₃

torus-H₁ : GroupEquiv (H̃ᶜʷ torusCW 1) (AbGroup→Group ℤ[Fin 2 ])
torus-H₁ = TorusProduct.H₁

private
  rank-one : GroupIso (AbGroup→Group ℤ[Fin 1 ]) ℤGroup
  Iso.fun (fst rank-one) f = f fzero
  Iso.inv (fst rank-one) z _ = z
  Iso.sec (fst rank-one) z = refl
  Iso.ret (fst rank-one) f = funExt λ k → cong f (snd isContrFin1 k)
  snd rank-one = makeIsGroupHom λ _ _ → refl

torus-H₂ : GroupEquiv (H̃ᶜʷ torusCW 2) ℤGroup
torus-H₂ = compGroupEquiv TorusProduct.H₂ (GroupIso→GroupEquiv rank-one)

torus-H₃ : Hzero torusCW 3
torus-H₃ = TorusProduct.H₃

graph-h graph-a graph-b : fst (H̃ᶜʷ graph×circleCW 1)
graph-h = GraphProduct.edge-generator fzero
graph-a = GraphProduct.edge-generator (fsuc fzero)
graph-b = GraphProduct.edge-generator (fsuc (fsuc fzero))

graph-a×h graph-b×h : fst (H̃ᶜʷ graph×circleCW 2)
graph-a×h = GraphProduct.square-generator fzero
graph-b×h = GraphProduct.square-generator (fsuc fzero)

graph-square-pair : fst (H̃ᶜʷ graph×circleCW 2) → ℤ × ℤ
graph-square-pair z = GraphProduct.square-coordinate z fzero ,
  GraphProduct.square-coordinate z (fsuc fzero)

abstract
  graph-a×h-coordinate : graph-square-pair graph-a×h ≡ (pos 1 , pos 0)
  graph-a×h-coordinate = cong (λ f → f fzero , f (fsuc fzero))
    (GraphProduct.square-generator-coordinate fzero)

  graph-b×h-coordinate : graph-square-pair graph-b×h ≡ (pos 0 , pos 1)
  graph-b×h-coordinate = cong (λ f → f fzero , f (fsuc fzero))
    (GraphProduct.square-generator-coordinate (fsuc fzero))

torus-a×h : fst (H̃ᶜʷ torusCW 2)
torus-a×h = TorusProduct.square-generator fzero

torus-square-coordinate : fst (H̃ᶜʷ torusCW 2) → ℤ
torus-square-coordinate = fst (fst torus-H₂)

abstract
  torus-a×h-coordinate : torus-square-coordinate torus-a×h ≡ pos 1
  torus-a×h-coordinate = cong (λ f → f fzero)
    (TorusProduct.square-generator-coordinate fzero)
