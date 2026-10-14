{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.Generators where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import DeloopS3.Bridge.CoverChains.OrbitSums
open import DeloopS3.Bridge.CoverChains.Incidence
open import DeloopS3.Bridge.CoverChains.Words
open import DeloopS3.Bridge.CoverChains.Complex
open import DeloopS3.Cert.Input.Initial.Faces using (initial-winding)
import DeloopS3.Bridge.SeifertChains.Matrices as Base
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

-- Coordinates of a single target torus (and of its core circle).
targetTorus : Kind → ℤ → fst Base.ℤ³
targetTorus A t = t , pos 0 , pos 0
targetTorus B t = pos 0 , t , pos 0
targetTorus C t = pos 0 , pos 0 , t

abstract
  F₃-basis : (c : ShortCase) (k : Kind) (b : Bd c k)
    → F₃ c (basis c (k , b)) ≡ targetTorus k (pos (suc (ellPred c k b)))
  F₃-basis octa A fzero = refl
  F₃-basis octa A (fsuc fzero) = refl
  F₃-basis octa A (fsuc (fsuc ()))
  F₃-basis octa B fzero = refl
  F₃-basis octa B (fsuc ())
  F₃-basis octa C fzero = refl
  F₃-basis octa C (fsuc fzero) = refl
  F₃-basis octa C (fsuc (fsuc ()))
  F₃-basis icosa A fzero = refl
  F₃-basis icosa A (fsuc fzero) = refl
  F₃-basis icosa A (fsuc (fsuc fzero)) = refl
  F₃-basis icosa A (fsuc (fsuc (fsuc fzero))) = refl
  F₃-basis icosa A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  F₃-basis icosa A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  F₃-basis icosa A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  F₃-basis icosa B fzero = refl
  F₃-basis icosa B (fsuc fzero) = refl
  F₃-basis icosa B (fsuc (fsuc fzero)) = refl
  F₃-basis icosa B (fsuc (fsuc (fsuc fzero))) = refl
  F₃-basis icosa B (fsuc (fsuc (fsuc (fsuc ()))))
  F₃-basis icosa C fzero = refl
  F₃-basis icosa C (fsuc fzero) = refl
  F₃-basis icosa C (fsuc (fsuc ()))

  U₀-basis : (c : ShortCase) (k : Kind) (b : Bd c k)
    → fst (U₀ c) (basis c (k , b)) ≡ targetTorus k (pos 1)
  U₀-basis octa A fzero = refl
  U₀-basis octa A (fsuc fzero) = refl
  U₀-basis octa A (fsuc (fsuc ()))
  U₀-basis octa B fzero = refl
  U₀-basis octa B (fsuc ())
  U₀-basis octa C fzero = refl
  U₀-basis octa C (fsuc fzero) = refl
  U₀-basis octa C (fsuc (fsuc ()))
  U₀-basis icosa A fzero = refl
  U₀-basis icosa A (fsuc fzero) = refl
  U₀-basis icosa A (fsuc (fsuc fzero)) = refl
  U₀-basis icosa A (fsuc (fsuc (fsuc fzero))) = refl
  U₀-basis icosa A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  U₀-basis icosa A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  U₀-basis icosa A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  U₀-basis icosa B fzero = refl
  U₀-basis icosa B (fsuc fzero) = refl
  U₀-basis icosa B (fsuc (fsuc fzero)) = refl
  U₀-basis icosa B (fsuc (fsuc (fsuc fzero))) = refl
  U₀-basis icosa B (fsuc (fsuc (fsuc (fsuc ()))))
  U₀-basis icosa C fzero = refl
  U₀-basis icosa C (fsuc fzero) = refl
  U₀-basis icosa C (fsuc (fsuc ()))

  initial-right-weight : (c : ShortCase) (k : Kind) (b : Bd c k)
    → R.int (Ch.faceWeight (R.faceAt (S₀ c) (faceIndex c (k , b)))) ≡ localWeight c k
  initial-right-weight octa A fzero = refl
  initial-right-weight octa A (fsuc fzero) = refl
  initial-right-weight octa A (fsuc (fsuc ()))
  initial-right-weight octa B fzero = refl
  initial-right-weight octa B (fsuc ())
  initial-right-weight octa C fzero = refl
  initial-right-weight octa C (fsuc fzero) = refl
  initial-right-weight octa C (fsuc (fsuc ()))
  initial-right-weight icosa A fzero = refl
  initial-right-weight icosa A (fsuc fzero) = refl
  initial-right-weight icosa A (fsuc (fsuc fzero)) = refl
  initial-right-weight icosa A (fsuc (fsuc (fsuc fzero))) = refl
  initial-right-weight icosa A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  initial-right-weight icosa A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  initial-right-weight icosa A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  initial-right-weight icosa B fzero = refl
  initial-right-weight icosa B (fsuc fzero) = refl
  initial-right-weight icosa B (fsuc (fsuc fzero)) = refl
  initial-right-weight icosa B (fsuc (fsuc (fsuc fzero))) = refl
  initial-right-weight icosa B (fsuc (fsuc (fsuc (fsuc ()))))
  initial-right-weight icosa C fzero = refl
  initial-right-weight icosa C (fsuc fzero) = refl
  initial-right-weight icosa C (fsuc (fsuc ()))

  initial-right-order : (c : ShortCase) (k : Kind) (b : Bd c k)
    → Ch.faceOrder (R.faceAt (S₀ c) (faceIndex c (k , b))) ≡ suc (orderPred c k b)
  initial-right-order octa A fzero = refl
  initial-right-order octa A (fsuc fzero) = refl
  initial-right-order octa A (fsuc (fsuc ()))
  initial-right-order octa B fzero = refl
  initial-right-order octa B (fsuc ())
  initial-right-order octa C fzero = refl
  initial-right-order octa C (fsuc fzero) = refl
  initial-right-order octa C (fsuc (fsuc ()))
  initial-right-order icosa A fzero = refl
  initial-right-order icosa A (fsuc fzero) = refl
  initial-right-order icosa A (fsuc (fsuc fzero)) = refl
  initial-right-order icosa A (fsuc (fsuc (fsuc fzero))) = refl
  initial-right-order icosa A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  initial-right-order icosa A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  initial-right-order icosa A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  initial-right-order icosa B fzero = refl
  initial-right-order icosa B (fsuc fzero) = refl
  initial-right-order icosa B (fsuc (fsuc fzero)) = refl
  initial-right-order icosa B (fsuc (fsuc (fsuc fzero))) = refl
  initial-right-order icosa B (fsuc (fsuc (fsuc (fsuc ()))))
  initial-right-order icosa C fzero = refl
  initial-right-order icosa C (fsuc fzero) = refl
  initial-right-order icosa C (fsuc (fsuc ()))

  initial-fibre-winding-zero : (c : ShortCase) (b : Bdy c)
    → Ch.faceH (R.faceAt (S₀ c) (faceIndex c b)) ≡ P.pos 0
  initial-fibre-winding-zero c b = initial-winding c (faceIndex c b)

  cover-torus-prism-boundary : (c : ShortCase) (b : Bdy c)
    → fst (ChainComplex.bdry (Kcov c) 3) (basis c b)
      ≡ (initialExponent c b , AbGroupStr.0g (snd (Overlap₁ c)))
  cover-torus-prism-boundary c b = ΣPathP
    (funExt (Dhat-basis-initial-word c b) , refl)
