{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.CartesianFromFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Sigma using (Σ-cong-equiv-snd; ΣPathP)
open import Cubical.Functions.Fibration using (totalEquiv)
import DeloopS3.Sphere.TruncationCartesian as TC

module _ {R N E B : Type}
  (u : R → N) (p : E → B) (α : R → E) (j : N → B)
  (H : (r : R) → p (α r) ≡ j (u r)) where

  vertical-map : (n : N) → fiber u n → fiber p (j n)
  vertical-map n (r , q) = α r , H r ∙ cong j q

  abstract
    cartesian-from-fibers : ((n : N) → isEquiv (vertical-map n))
      → TC.CartSquare u p α j H
    TC.CartSquare.comparison-isEquiv (cartesian-from-fibers all) =
      subst isEquiv (funExt comparison-path) (snd total-comparison)
      where
      total-comparison : R ≃ TC.PB p j
      total-comparison = compEquiv (totalEquiv u)
        (Σ-cong-equiv-snd (λ n → vertical-map n , all n))

      comparison-path : (r : R)
        → equivFun total-comparison r ≡ TC.squareComparison u p α j H r
      comparison-path r = ΣPathP (refl , ΣPathP (refl , sym (rUnit (H r))))
