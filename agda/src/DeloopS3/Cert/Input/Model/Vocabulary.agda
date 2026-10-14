{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Model.Vocabulary where

-- Short's fixed groups, letters, actions, and ShortInput record.
-- firstSheet-value identifies startOf without unfolding the proof-dependent
-- firstSheetAt, so ShortInput.orbit-start retains its specified endpoint.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (true)
open import Cubical.Data.List.Base using (List; []; _∷_)
import Cubical.Data.Int as Z
import Cubical.Data.SumFin as SF
open SF using (fzero; fsuc)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Interpret.Short as Short
open import DeloopS3.Cert.Interpret.Short public using
  (ShortCase; octa; icosa; certOf; Sheet; BaseLetter; a+; a-; b+; b-;
   wireLetter; rawChecks; actEquiv; actFin; localPermutation;
   Δ; H; j; letterElement; repElement; ShortInput)
open import DeloopS3.Cert.Interpret.Syntax public using (RawChecks; twoGenerators)
open import DeloopS3.Groups.TablePermutation using (at)
open import Cubical.Algebra.Group.Base using (GroupStr)

Sh : ShortCase → Type₀
Sh c = Sheet (certOf c)
S₀ : ShortCase → Ch.State
S₀ c = Ch.initialState (certOf c)
gs : ShortCase → List ℕ
gs c = Ch.alive (S₀ c)
Γ : Type₀
Γ = R.Rose twoGenerators

wireWord : List BaseLetter → P.Word
wireWord = P.map wireLetter
baseWord : Ch.Kind → List BaseLetter
baseWord Ch.A = a+ ∷ []
baseWord Ch.B = b+ ∷ []
baseWord Ch.C = b- ∷ a- ∷ []

baseWord-wire : (k : Ch.Kind) → wireWord (baseWord k) ≡ Ch.kindWord k
baseWord-wire Ch.A = refl
baseWord-wire Ch.B = refl
baseWord-wire Ch.C = refl

genElement : (c : ShortCase) → Ch.Kind → Δ c .fst
genElement c Ch.A = letterElement c a+
genElement c Ch.B = letterElement c b+
genElement c Ch.C = GroupStr.inv (Δ c .snd)
  (GroupStr._·_ (Δ c .snd) (letterElement c a+) (letterElement c b+))

localOrder : ShortCase → Ch.Kind → ℕ
localOrder c Ch.A = 2
localOrder c Ch.B = 3
localOrder octa Ch.C = 4
localOrder icosa Ch.C = 5
localWeight : ShortCase → Ch.Kind → Z.ℤ
localWeight c Ch.A = Z.pos 1
localWeight c Ch.B = Z.pos 1
localWeight octa Ch.C = Z.negsuc 2
localWeight icosa Ch.C = Z.negsuc 3

bdList : ShortCase → Ch.Kind → List Ch.Boundary
bdList c = Short.boundariesOf (certOf c)
Bd : ShortCase → Ch.Kind → Type₀
Bd c k = SF.Fin (P.length (bdList c k))
bdAt : (c : ShortCase) (k : Ch.Kind) → Bd c k → Ch.Boundary
bdAt c k = at (bdList c k)

startOf : (c : ShortCase) (k : Ch.Kind) → Bd c k → Sh c
startOf octa Ch.A fzero = fzero
startOf octa Ch.A (fsuc fzero) = (fsuc (fsuc fzero))
startOf octa Ch.B fzero = fzero
startOf octa Ch.C fzero = fzero
startOf octa Ch.C (fsuc fzero) = (fsuc fzero)
startOf icosa Ch.A fzero = fzero
startOf icosa Ch.A (fsuc fzero) = (fsuc (fsuc fzero))
startOf icosa Ch.A (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc fzero)))
startOf icosa Ch.A (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
startOf icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
startOf icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
startOf icosa Ch.B fzero = fzero
startOf icosa Ch.B (fsuc fzero) = (fsuc fzero)
startOf icosa Ch.B (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc (fsuc fzero))))
startOf icosa Ch.B (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
startOf icosa Ch.C fzero = fzero
startOf icosa Ch.C (fsuc fzero) = (fsuc (fsuc (fsuc fzero)))
startOf octa Ch.A (fsuc (fsuc ()))
startOf octa Ch.B (fsuc ())
startOf octa Ch.C (fsuc (fsuc ()))
startOf icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
startOf icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
startOf icosa Ch.C (fsuc (fsuc ()))

ellPred : (c : ShortCase) (k : Ch.Kind) → Bd c k → ℕ
ellPred octa Ch.A fzero = 1
ellPred octa Ch.A (fsuc fzero) = 0
ellPred octa Ch.B fzero = 2
ellPred octa Ch.C fzero = 0
ellPred octa Ch.C (fsuc fzero) = 1
ellPred icosa Ch.A fzero = 1
ellPred icosa Ch.A (fsuc fzero) = 1
ellPred icosa Ch.A (fsuc (fsuc fzero)) = 1
ellPred icosa Ch.A (fsuc (fsuc (fsuc fzero))) = 1
ellPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = 0
ellPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = 0
ellPred icosa Ch.B fzero = 0
ellPred icosa Ch.B (fsuc fzero) = 2
ellPred icosa Ch.B (fsuc (fsuc fzero)) = 2
ellPred icosa Ch.B (fsuc (fsuc (fsuc fzero))) = 2
ellPred icosa Ch.C fzero = 4
ellPred icosa Ch.C (fsuc fzero) = 4
ellPred octa Ch.A (fsuc (fsuc ()))
ellPred octa Ch.B (fsuc ())
ellPred octa Ch.C (fsuc (fsuc ()))
ellPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
ellPred icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
ellPred icosa Ch.C (fsuc (fsuc ()))

orderPred : (c : ShortCase) (k : Ch.Kind) → Bd c k → ℕ
orderPred octa Ch.A fzero = 0
orderPred octa Ch.A (fsuc fzero) = 1
orderPred octa Ch.B fzero = 0
orderPred octa Ch.C fzero = 3
orderPred octa Ch.C (fsuc fzero) = 1
orderPred icosa Ch.A fzero = 0
orderPred icosa Ch.A (fsuc fzero) = 0
orderPred icosa Ch.A (fsuc (fsuc fzero)) = 0
orderPred icosa Ch.A (fsuc (fsuc (fsuc fzero))) = 0
orderPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = 1
orderPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = 1
orderPred icosa Ch.B fzero = 2
orderPred icosa Ch.B (fsuc fzero) = 0
orderPred icosa Ch.B (fsuc (fsuc fzero)) = 0
orderPred icosa Ch.B (fsuc (fsuc (fsuc fzero))) = 0
orderPred icosa Ch.C fzero = 0
orderPred icosa Ch.C (fsuc fzero) = 0
orderPred octa Ch.A (fsuc (fsuc ()))
orderPred octa Ch.B (fsuc ())
orderPred octa Ch.C (fsuc (fsuc ()))
orderPred icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
orderPred icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
orderPred icosa Ch.C (fsuc (fsuc ()))

bdAllAt : (c : ShortCase) → R.FaceIx (S₀ c) → Ch.Boundary
bdAllAt octa = at (Ch.boundaries (certOf octa))
bdAllAt icosa = at (Ch.boundaries (certOf icosa))

allBoundaryIndex : (c : ShortCase) → (Σ[ k ∈ Ch.Kind ] Bd c k) ≃ R.FaceIx (S₀ c)
allBoundaryIndex octa = isoToEquiv (iso forward backward sec ret)
  where
  forward : (Σ[ k ∈ Ch.Kind ] Bd octa k) → R.FaceIx (S₀ octa)
  forward (Ch.A , fzero) = fzero
  forward (Ch.A , (fsuc fzero)) = (fsuc fzero)
  forward (Ch.A , (fsuc (fsuc ())))
  forward (Ch.B , fzero) = (fsuc (fsuc fzero))
  forward (Ch.B , (fsuc ()))
  forward (Ch.C , fzero) = (fsuc (fsuc (fsuc fzero)))
  forward (Ch.C , (fsuc fzero)) = (fsuc (fsuc (fsuc (fsuc fzero))))
  forward (Ch.C , (fsuc (fsuc ())))
  backward : R.FaceIx (S₀ octa) → (Σ[ k ∈ Ch.Kind ] Bd octa k)
  backward fzero = Ch.A , fzero
  backward (fsuc fzero) = Ch.A , (fsuc fzero)
  backward (fsuc (fsuc fzero)) = Ch.B , fzero
  backward (fsuc (fsuc (fsuc fzero))) = Ch.C , fzero
  backward (fsuc (fsuc (fsuc (fsuc fzero)))) = Ch.C , (fsuc fzero)
  backward (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  sec : (i : R.FaceIx (S₀ octa)) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ret : (i : Σ[ k ∈ Ch.Kind ] Bd octa k) → backward (forward i) ≡ i
  ret (Ch.A , fzero) = refl
  ret (Ch.A , (fsuc fzero)) = refl
  ret (Ch.A , (fsuc (fsuc ())))
  ret (Ch.B , fzero) = refl
  ret (Ch.B , (fsuc ()))
  ret (Ch.C , fzero) = refl
  ret (Ch.C , (fsuc fzero)) = refl
  ret (Ch.C , (fsuc (fsuc ())))
allBoundaryIndex icosa = isoToEquiv (iso forward backward sec ret)
  where
  forward : (Σ[ k ∈ Ch.Kind ] Bd icosa k) → R.FaceIx (S₀ icosa)
  forward (Ch.A , fzero) = fzero
  forward (Ch.A , (fsuc fzero)) = (fsuc fzero)
  forward (Ch.A , (fsuc (fsuc fzero))) = (fsuc (fsuc fzero))
  forward (Ch.A , (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc fzero)))
  forward (Ch.A , (fsuc (fsuc (fsuc (fsuc fzero))))) = (fsuc (fsuc (fsuc (fsuc fzero))))
  forward (Ch.A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
  forward (Ch.A , (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))
  forward (Ch.B , fzero) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
  forward (Ch.B , (fsuc fzero)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
  forward (Ch.B , (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
  forward (Ch.B , (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
  forward (Ch.B , (fsuc (fsuc (fsuc (fsuc ())))))
  forward (Ch.C , fzero) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
  forward (Ch.C , (fsuc fzero)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))
  forward (Ch.C , (fsuc (fsuc ())))
  backward : R.FaceIx (S₀ icosa) → (Σ[ k ∈ Ch.Kind ] Bd icosa k)
  backward fzero = Ch.A , fzero
  backward (fsuc fzero) = Ch.A , (fsuc fzero)
  backward (fsuc (fsuc fzero)) = Ch.A , (fsuc (fsuc fzero))
  backward (fsuc (fsuc (fsuc fzero))) = Ch.A , (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc (fsuc fzero)))) = Ch.A , (fsuc (fsuc (fsuc (fsuc fzero))))
  backward (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = Ch.A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = Ch.B , fzero
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = Ch.B , (fsuc fzero)
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = Ch.B , (fsuc (fsuc fzero))
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = Ch.B , (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = Ch.C , fzero
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = Ch.C , (fsuc fzero)
  backward (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))))
  sec : (i : R.FaceIx (S₀ icosa)) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))))
  ret : (i : Σ[ k ∈ Ch.Kind ] Bd icosa k) → backward (forward i) ≡ i
  ret (Ch.A , fzero) = refl
  ret (Ch.A , (fsuc fzero)) = refl
  ret (Ch.A , (fsuc (fsuc fzero))) = refl
  ret (Ch.A , (fsuc (fsuc (fsuc fzero)))) = refl
  ret (Ch.A , (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  ret (Ch.A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  ret (Ch.A , (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))
  ret (Ch.B , fzero) = refl
  ret (Ch.B , (fsuc fzero)) = refl
  ret (Ch.B , (fsuc (fsuc fzero))) = refl
  ret (Ch.B , (fsuc (fsuc (fsuc fzero)))) = refl
  ret (Ch.B , (fsuc (fsuc (fsuc (fsuc ())))))
  ret (Ch.C , fzero) = refl
  ret (Ch.C , (fsuc fzero)) = refl
  ret (Ch.C , (fsuc (fsuc ())))

abstract
  startOf-value : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → SF.toℕ (startOf c k b) ≡ P.nth 0 (Ch.orbit (bdAt c k b)) 0
  ellPred-value : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → suc (ellPred c k b) ≡ Ch.orbitLength (bdAt c k b)
  orderPred-value : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → suc (orderPred c k b) ≡ Ch.order (bdAt c k b)
  startOf-value octa Ch.A fzero = refl
  startOf-value octa Ch.A (fsuc fzero) = refl
  startOf-value octa Ch.A (fsuc (fsuc ()))
  startOf-value octa Ch.B fzero = refl
  startOf-value octa Ch.B (fsuc ())
  startOf-value octa Ch.C fzero = refl
  startOf-value octa Ch.C (fsuc fzero) = refl
  startOf-value octa Ch.C (fsuc (fsuc ()))
  startOf-value icosa Ch.A fzero = refl
  startOf-value icosa Ch.A (fsuc fzero) = refl
  startOf-value icosa Ch.A (fsuc (fsuc fzero)) = refl
  startOf-value icosa Ch.A (fsuc (fsuc (fsuc fzero))) = refl
  startOf-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  startOf-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  startOf-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  startOf-value icosa Ch.B fzero = refl
  startOf-value icosa Ch.B (fsuc fzero) = refl
  startOf-value icosa Ch.B (fsuc (fsuc fzero)) = refl
  startOf-value icosa Ch.B (fsuc (fsuc (fsuc fzero))) = refl
  startOf-value icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
  startOf-value icosa Ch.C fzero = refl
  startOf-value icosa Ch.C (fsuc fzero) = refl
  startOf-value icosa Ch.C (fsuc (fsuc ()))
  ellPred-value octa Ch.A fzero = refl
  ellPred-value octa Ch.A (fsuc fzero) = refl
  ellPred-value octa Ch.A (fsuc (fsuc ()))
  ellPred-value octa Ch.B fzero = refl
  ellPred-value octa Ch.B (fsuc ())
  ellPred-value octa Ch.C fzero = refl
  ellPred-value octa Ch.C (fsuc fzero) = refl
  ellPred-value octa Ch.C (fsuc (fsuc ()))
  ellPred-value icosa Ch.A fzero = refl
  ellPred-value icosa Ch.A (fsuc fzero) = refl
  ellPred-value icosa Ch.A (fsuc (fsuc fzero)) = refl
  ellPred-value icosa Ch.A (fsuc (fsuc (fsuc fzero))) = refl
  ellPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  ellPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  ellPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  ellPred-value icosa Ch.B fzero = refl
  ellPred-value icosa Ch.B (fsuc fzero) = refl
  ellPred-value icosa Ch.B (fsuc (fsuc fzero)) = refl
  ellPred-value icosa Ch.B (fsuc (fsuc (fsuc fzero))) = refl
  ellPred-value icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
  ellPred-value icosa Ch.C fzero = refl
  ellPred-value icosa Ch.C (fsuc fzero) = refl
  ellPred-value icosa Ch.C (fsuc (fsuc ()))
  orderPred-value octa Ch.A fzero = refl
  orderPred-value octa Ch.A (fsuc fzero) = refl
  orderPred-value octa Ch.A (fsuc (fsuc ()))
  orderPred-value octa Ch.B fzero = refl
  orderPred-value octa Ch.B (fsuc ())
  orderPred-value octa Ch.C fzero = refl
  orderPred-value octa Ch.C (fsuc fzero) = refl
  orderPred-value octa Ch.C (fsuc (fsuc ()))
  orderPred-value icosa Ch.A fzero = refl
  orderPred-value icosa Ch.A (fsuc fzero) = refl
  orderPred-value icosa Ch.A (fsuc (fsuc fzero)) = refl
  orderPred-value icosa Ch.A (fsuc (fsuc (fsuc fzero))) = refl
  orderPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  orderPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  orderPred-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  orderPred-value icosa Ch.B fzero = refl
  orderPred-value icosa Ch.B (fsuc fzero) = refl
  orderPred-value icosa Ch.B (fsuc (fsuc fzero)) = refl
  orderPred-value icosa Ch.B (fsuc (fsuc (fsuc fzero))) = refl
  orderPred-value icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
  orderPred-value icosa Ch.C fzero = refl
  orderPred-value icosa Ch.C (fsuc fzero) = refl
  orderPred-value icosa Ch.C (fsuc (fsuc ()))

abstract
  bdAt-kind : (c : ShortCase) (k : Ch.Kind) (b : Bd c k) → Ch.kind (bdAt c k b) ≡ k
  bdAt-kind octa Ch.A fzero = refl
  bdAt-kind octa Ch.A (fsuc fzero) = refl
  bdAt-kind octa Ch.A (fsuc (fsuc ()))
  bdAt-kind octa Ch.B fzero = refl
  bdAt-kind octa Ch.B (fsuc ())
  bdAt-kind octa Ch.C fzero = refl
  bdAt-kind octa Ch.C (fsuc fzero) = refl
  bdAt-kind octa Ch.C (fsuc (fsuc ()))
  bdAt-kind icosa Ch.A fzero = refl
  bdAt-kind icosa Ch.A (fsuc fzero) = refl
  bdAt-kind icosa Ch.A (fsuc (fsuc fzero)) = refl
  bdAt-kind icosa Ch.A (fsuc (fsuc (fsuc fzero))) = refl
  bdAt-kind icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  bdAt-kind icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  bdAt-kind icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  bdAt-kind icosa Ch.B fzero = refl
  bdAt-kind icosa Ch.B (fsuc fzero) = refl
  bdAt-kind icosa Ch.B (fsuc (fsuc fzero)) = refl
  bdAt-kind icosa Ch.B (fsuc (fsuc (fsuc fzero))) = refl
  bdAt-kind icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
  bdAt-kind icosa Ch.C fzero = refl
  bdAt-kind icosa Ch.C (fsuc fzero) = refl
  bdAt-kind icosa Ch.C (fsuc (fsuc ()))

  allBoundaryIndex-boundary : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → bdAllAt c (equivFun (allBoundaryIndex c) (k , b)) ≡ bdAt c k b
  allBoundaryIndex-boundary octa Ch.A fzero = refl
  allBoundaryIndex-boundary octa Ch.A (fsuc fzero) = refl
  allBoundaryIndex-boundary octa Ch.A (fsuc (fsuc ()))
  allBoundaryIndex-boundary octa Ch.B fzero = refl
  allBoundaryIndex-boundary octa Ch.B (fsuc ())
  allBoundaryIndex-boundary octa Ch.C fzero = refl
  allBoundaryIndex-boundary octa Ch.C (fsuc fzero) = refl
  allBoundaryIndex-boundary octa Ch.C (fsuc (fsuc ()))
  allBoundaryIndex-boundary icosa Ch.A fzero = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc fzero) = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc (fsuc fzero)) = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc (fsuc (fsuc fzero))) = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  allBoundaryIndex-boundary icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))
  allBoundaryIndex-boundary icosa Ch.B fzero = refl
  allBoundaryIndex-boundary icosa Ch.B (fsuc fzero) = refl
  allBoundaryIndex-boundary icosa Ch.B (fsuc (fsuc fzero)) = refl
  allBoundaryIndex-boundary icosa Ch.B (fsuc (fsuc (fsuc fzero))) = refl
  allBoundaryIndex-boundary icosa Ch.B (fsuc (fsuc (fsuc (fsuc ()))))
  allBoundaryIndex-boundary icosa Ch.C fzero = refl
  allBoundaryIndex-boundary icosa Ch.C (fsuc fzero) = refl
  allBoundaryIndex-boundary icosa Ch.C (fsuc (fsuc ()))
