{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Faces where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Data.Nat using (_<ᵇ_; _≡ᵇ_; _·_)
open import Cubical.Data.Bool using (true)
import Cubical.Data.Int as Z
import Cubical.HITs.S1.Base as S1
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop-1g)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (rUnitₖ)
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Initial.Boundary using (boundary-checked)
open import DeloopS3.Cert.Interpret.Syntax using (and-left; and-right; zEq-sound)
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

abstract
  initial-face : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → R.faceAt (S₀ c) b ≡ Ch.faceOf (bdAllAt c b)
  initial-face octa fzero = refl
  initial-face octa (fsuc fzero) = refl
  initial-face octa (fsuc (fsuc fzero)) = refl
  initial-face octa (fsuc (fsuc (fsuc fzero))) = refl
  initial-face octa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  initial-face octa (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  initial-face icosa fzero = refl
  initial-face icosa (fsuc fzero) = refl
  initial-face icosa (fsuc (fsuc fzero)) = refl
  initial-face icosa (fsuc (fsuc (fsuc fzero))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) = refl
  initial-face icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))))

  boundary-zero : (ct : Ch.Certificate) (bd : Ch.Boundary)
    → Ch.checkBoundary ct bd ≡ true → Ch.hPower bd ≡ P.pos 0
  boundary-zero ct bd ok = zEq-sound _ _ (and-left
    (and-right {a = P.zEq (Ch.weight bd) (Ch.kindWeight ct (Ch.kind bd))}
    (and-right {a = (Ch.orbitLength bd · Ch.order bd ≡ᵇ P.nth 0 (Ch.orders ct) (Ch.kindIndex (Ch.kind bd)))}
    (and-right {a = (P.length (Ch.orbit bd) ≡ᵇ Ch.orbitLength bd)}
    (and-right {a = P.tableEq (P.map (λ i → P.fst (Ch.liftWord ct i (Ch.kindWord (Ch.kind bd)))) (Ch.orbit bd)) (Ch.rotate (Ch.orbit bd))}
    (and-right {a = P.all (λ i → i <ᵇ Ch.index ct) (Ch.orbit bd)}
    (and-right {a = 0 <ᵇ P.length (Ch.orbit bd)} ok)))))))

  initial-word : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → Ch.faceWord (R.faceAt (S₀ c) b) ≡ Ch.boundaryWord (bdAllAt c b)
  initial-word c b = cong Ch.faceWord (initial-face c b)

  initial-winding : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → Ch.faceH (R.faceAt (S₀ c) b) ≡ P.pos 0
  initial-winding c b = cong Ch.faceH (initial-face c b)
    ∙ boundary-zero (certOf c) (bdAllAt c b) (boundary-checked c b)

  mul-zero-S¹ : (u : S1.S¹) → R.mulC (Z.pos 0) (Circle.circleToC u) ≡ R.0C
  mul-zero-S¹ S1.base = refl
  mul-zero-S¹ (S1.loop i) j = emloop-1g ℤGroup j i

  mul-zero : (u : R.C) → R.mulC (Z.pos 0) u ≡ R.0C
  mul-zero u = sym (cong (R.mulC (Z.pos 0)) (Circle.circle-retraction u))
    ∙ mul-zero-S¹ (Circle.CToCircle u)

  zero-winding : (u t : R.C) → t R.+C R.mulC (Z.pos 0) u ≡ t
  zero-winding u t = cong (t R.+C_) (mul-zero u) ∙ rUnitₖ {G = ℤAbGroup} 1 t

  initial-fibre : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u t : R.C)
    → t R.+C R.mulC (R.int (Ch.faceH (R.faceAt (S₀ c) b))) u ≡ t
  initial-fibre c b u t = cong (λ h → t R.+C R.mulC (R.int h) u) (initial-winding c b)
    ∙ zero-winding u t
