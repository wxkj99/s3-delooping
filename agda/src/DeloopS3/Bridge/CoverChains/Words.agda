{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.Words where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; _≡ᵇ_)
open import Cubical.Data.Bool using (true; false; if_then_else_)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.SumFin using (fzero; fsuc; toℕ)
open import Cubical.Data.Int using (ℤ; pos; negsuc; _+_)
open import DeloopS3.Bridge.CoverChains.Incidence
open import DeloopS3.Bridge.CoverChains.OrbitSums
open import DeloopS3.Cert.Input.Graph.Maps using (Petal)
open import DeloopS3.Cert.Input.Initial.Faces using (initial-word; initial-fibre)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

-- The allBoundaryIndex permutation is deliberately retained in this API.
faceIndex : (c : ShortCase) → Bdy c → R.FaceIx (S₀ c)
faceIndex c = equivFun (allBoundaryIndex c)

basis : (c : ShortCase) → Bdy c → fst (Tori c)
basis c b b′ = if toℕ (faceIndex c b) ≡ᵇ toℕ (faceIndex c b′) then pos 1 else pos 0

wordExponent : ℕ → P.Word → ℤ
wordExponent j [] = pos 0
wordExponent j (P.fwd k ∷ w) = (if j ≡ᵇ k then pos 1 else pos 0) + wordExponent j w
wordExponent j (P.bwd k ∷ w) = (if j ≡ᵇ k then negsuc 0 else pos 0) + wordExponent j w

initialExponent : (c : ShortCase) → Bdy c → Petal c → ℤ
initialExponent c b j = wordExponent (P.nth 0 (gs c) (toℕ j))
  (Ch.faceWord (R.faceAt (S₀ c) (faceIndex c b)))

-- Coefficients are computed from the actual initial boundary words,
-- not against their values in the finite triangle group. Together with
-- raw-cycle this identifies Dhat with tree-collapsed boundary incidence.
abstract
  Dhat-basis-initial-word : (c : ShortCase) (b : Bdy c) (j : Petal c)
    → fst (Dhat c) (basis c b) j ≡ initialExponent c b j
  Dhat-basis-initial-word octa (A , fzero) fzero = refl
  Dhat-basis-initial-word octa (A , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word octa (A , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word octa (A , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word octa (A , fzero) (fsuc (fsuc (fsuc (fsuc ()))))
  Dhat-basis-initial-word octa (A , (fsuc fzero)) fzero = refl
  Dhat-basis-initial-word octa (A , (fsuc fzero)) (fsuc fzero) = refl
  Dhat-basis-initial-word octa (A , (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word octa (A , (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word octa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc ()))))
  Dhat-basis-initial-word octa (A , (fsuc (fsuc ()))) j
  Dhat-basis-initial-word octa (B , fzero) fzero = refl
  Dhat-basis-initial-word octa (B , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word octa (B , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word octa (B , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word octa (B , fzero) (fsuc (fsuc (fsuc (fsuc ()))))
  Dhat-basis-initial-word octa (B , (fsuc ())) j
  Dhat-basis-initial-word octa (C , fzero) fzero = refl
  Dhat-basis-initial-word octa (C , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word octa (C , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word octa (C , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word octa (C , fzero) (fsuc (fsuc (fsuc (fsuc ()))))
  Dhat-basis-initial-word octa (C , (fsuc fzero)) fzero = refl
  Dhat-basis-initial-word octa (C , (fsuc fzero)) (fsuc fzero) = refl
  Dhat-basis-initial-word octa (C , (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word octa (C , (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word octa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc ()))))
  Dhat-basis-initial-word octa (C , (fsuc (fsuc ()))) j
  Dhat-basis-initial-word icosa (A , fzero) fzero = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) fzero = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) fzero = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) fzero = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) fzero = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (A , (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))) j
  Dhat-basis-initial-word icosa (B , fzero) fzero = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (B , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) fzero = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) fzero = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) fzero = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (B , (fsuc (fsuc (fsuc (fsuc ()))))) j
  Dhat-basis-initial-word icosa (C , fzero) fzero = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (C , fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) fzero = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc fzero) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  Dhat-basis-initial-word icosa (C , (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
  Dhat-basis-initial-word icosa (C , (fsuc (fsuc ()))) j
