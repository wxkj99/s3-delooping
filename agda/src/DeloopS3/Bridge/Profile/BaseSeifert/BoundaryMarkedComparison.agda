{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; cong-∙)
open import Cubical.Data.Fin using (fzero ; fsuc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.CW.Base using (realise)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; graph×circleSkel)
import DeloopS3.Bridge.ComponentHomology.BoundaryWords as Words
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (rose-chart)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; circle-retraction)
open import DeloopS3.Move.CancelMinimal using (0C)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryRealizationProof using
  (word-marking ; OriginalMarkedRealizationComparison
  ; original-core-realization ; concrete-core-realization
  ; boundary-realization-agreements-from-comparison)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison.Products public using
  (original-torus-concrete ; original-core-concrete)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Products using
  (BoundaryRealizationAgreements)

private
  rose-simple : RoseProduct.Rose 2 → Literal.P
  rose-simple (inl tt) = inr 0C
  rose-simple (inr ((0 , w) , x)) = inl (circleToC x)
  rose-simple (inr ((1 , w) , x)) = inr (circleToC x)
  rose-simple (push (0 , w) i) = Literal.edge (~ i)
  rose-simple (push (1 , w) i) = inr 0C

  swap : Literal.P → Literal.P
  swap (inl x) = inr x
  swap (inr x) = inl x
  swap (push tt i) = push tt (~ i)

  abstract
    rose-chart-simple : Path (RoseProduct.Rose 2 → Literal.P)
      (fst rose-chart) rose-simple
    rose-chart-simple = funExt comparison
      where
      comparison : (x : RoseProduct.Rose 2)
        → Path Literal.P (fst rose-chart x) (rose-simple x)
      comparison (inl tt) = refl
      comparison (inr ((0 , w) , x)) = refl
      comparison (inr ((1 , w) , x)) = refl
      -- The unswapped chart edge is definitionally edge ∙ refl.
      comparison (push (0 , w) i) j =
        cong (cong swap) (sym (rUnit Literal.edge)) j i
      comparison (push (1 , w) i) = refl

    simple-word-ret : (p : Literal.P)
      → Path Literal.P (rose-simple (Words.word-chart p)) p
    simple-word-ret (inl x) = cong inl (circle-retraction x)
    simple-word-ret (inr x) = cong inr (circle-retraction x)
    -- The two chart edges map to edge and refl, respectively.
    simple-word-ret (push tt i) j =
      (cong-∙ rose-simple (sym (push fzero)) (push (fsuc fzero))
        ∙ sym (rUnit Literal.edge)) j i

    rose-word-ret : (p : Literal.P)
      → Path Literal.P (fst rose-chart (Words.word-chart p)) p
    rose-word-ret p =
      funExt⁻ rose-chart-simple (Words.word-chart p) ∙ simple-word-ret p

abstract
  word-marking-id : Path (Literal.Core → Literal.Core) word-marking (λ x → x)
  word-marking-id = funExt λ (p , t) → ΣPathP (rose-word-ret p , refl)

  original-marked-realization-comparison : OriginalMarkedRealizationComparison
  original-marked-realization-comparison = original-torus-concrete ,
    (original-core-concrete
      ∙ sym (cong (λ (k : Literal.Core → Literal.Core) → concrete-core-realization ∘ k)
          word-marking-id))

  boundary-realization-agreements : BoundaryRealizationAgreements
  boundary-realization-agreements =
    boundary-realization-agreements-from-comparison original-marked-realization-comparison
