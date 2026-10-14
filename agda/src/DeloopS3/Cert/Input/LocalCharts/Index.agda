{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Index where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.SumFin using (fzero; fsuc)
open import DeloopS3.Cert.Input.Model.Vocabulary
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R

boundaryIndex : (c : ShortCase) → R.FaceIx (S₀ c) → Σ[ k ∈ Ch.Kind ] Bd c k
boundaryIndex c = invEq (allBoundaryIndex c)

kindAt : (c : ShortCase) → R.FaceIx (S₀ c) → Ch.Kind
kindAt c b = boundaryIndex c b .fst

localAt : (c : ShortCase) (b : R.FaceIx (S₀ c)) → Bd c (kindAt c b)
localAt c b = boundaryIndex c b .snd

record FaceData (c : ShortCase) (b : R.FaceIx (S₀ c)) : Type₀ where
  field
    kind-index : kindAt c b ≡ Ch.kind (bdAllAt c b)
    boundary-index : bdAt c (kindAt c b) (localAt c b) ≡ bdAllAt c b
    length-index : suc (ellPred c (kindAt c b) (localAt c b)) ≡ Ch.orbitLength (bdAllAt c b)
    weight-index : R.int (Ch.faceWeight (R.faceAt (S₀ c) b)) ≡ localWeight c (kindAt c b)
    order-index : Ch.faceOrder (R.faceAt (S₀ c) b) ≡ suc (orderPred c (kindAt c b) (localAt c b))
open FaceData public

abstract
  face-data : (c : ShortCase) (b : R.FaceIx (S₀ c)) → FaceData c b
  face-data octa fzero = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data octa (fsuc fzero) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data octa (fsuc (fsuc fzero)) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data octa (fsuc (fsuc (fsuc fzero))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data octa (fsuc (fsuc (fsuc (fsuc fzero)))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data octa (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  face-data icosa fzero = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc fzero) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc fzero)) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc fzero))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = record { kind-index = refl ; boundary-index = refl ; length-index = refl ; weight-index = refl ; order-index = refl }
  face-data icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))))
