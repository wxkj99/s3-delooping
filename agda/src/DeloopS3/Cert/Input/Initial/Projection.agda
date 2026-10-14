{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Projection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Int as Z
import Cubical.HITs.S1.Base as S1
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Initial.Walk
open import DeloopS3.Cert.Input.Initial.Boundary
open import DeloopS3.Cert.Input.Initial.Circle
open import DeloopS3.Cert.Input.LocalCharts.Charts using (startSheet)
import DeloopS3.Cover.Orientation.CircleModel as Circle
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

abstract
  project-signedEdge : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → cong (projectGraph c) (signedEdge c i t)
      ≡ R.evalLetter (R.loopAt twoGenerators) (wireLetter t)
  project-signedEdge c i a+ = cong-∙ (projectGraph c) (edge i ga) (cong vertex (nextSheet-action c i ga))
    ∙ sym (rUnit (R.evalLetter (R.loopAt twoGenerators) (wireLetter a+)))
  project-signedEdge c i b+ = cong-∙ (projectGraph c) (edge i gb) (cong vertex (nextSheet-action c i gb))
    ∙ sym (rUnit (R.evalLetter (R.loopAt twoGenerators) (wireLetter b+)))
  project-signedEdge c i a- = cong-∙ (projectGraph c) (sym (cong vertex (next-negative c i ga)))
      (sym (edge (actFin (certOf c) (rawChecks c) a- i) ga))
    ∙ sym (lUnit (R.evalLetter (R.loopAt twoGenerators) (wireLetter a-)))
  project-signedEdge c i b- = cong-∙ (projectGraph c) (sym (cong vertex (next-negative c i gb)))
      (sym (edge (actFin (certOf c) (rawChecks c) b- i) gb))
    ∙ sym (lUnit (R.evalLetter (R.loopAt twoGenerators) (wireLetter b-)))

  project-walkPath : (c : ShortCase) (i : Sh c) (w : List BaseLetter)
    → cong (projectGraph c) (walkPath c i w) ≡ R.roseWord twoGenerators (wireWord w)
  project-walkPath c i [] = refl
  project-walkPath c i (t ∷ ts) = cong-∙ (projectGraph c) (signedEdge c i t)
      (walkPath c (actFin (certOf c) (rawChecks c) t i) ts)
    ∙ cong₂ _∙_ (project-signedEdge c i t) (project-walkPath c (actFin (certOf c) (rawChecks c) t i) ts)

  project-boundaryLoop : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → cong (projectGraph c) (boundaryLoop c b)
      ≡ R.roseWord twoGenerators (wireWord (boundaryWalkWord c b))
  project-boundaryLoop c b = cong-∙ (projectGraph c)
      (walkPath c (startSheet c b) (boundaryWalkWord c b)) (cong vertex (CheckedBoundary.closed c b))
    ∙ sym (rUnit (cong (projectGraph c) (walkPath c (startSheet c b) (boundaryWalkWord c b))))
    ∙ project-walkPath c (startSheet c b) (boundaryWalkWord c b)

repeatWire : ℕ → P.Word → P.Word
repeatWire n w = P.concatMap (λ v → v) (P.replicate n w)

abstract
  append-unit : (w : P.Word) → w P.++ [] ≡ w
  append-unit [] = refl
  append-unit (t ∷ ts) = cong (t ∷_) (append-unit ts)

  append-assoc : (u v w : P.Word) → (u P.++ v) P.++ w ≡ u P.++ (v P.++ w)
  append-assoc [] v w = refl
  append-assoc (t ∷ ts) v w = cong (t ∷_) (append-assoc ts v w)

  repeat-snoc : (n : ℕ) (w : P.Word) → repeatWire (suc n) w ≡ repeatWire n w P.++ w
  repeat-snoc zero w = append-unit w
  repeat-snoc (suc n) w = cong (w P.++_) (repeat-snoc n w)
    ∙ sym (append-assoc w (repeatWire n w) w)

  word-intLoop : (gs : List ℕ) (w : P.Word) (n : ℕ)
    → cong (R.circleRec R.root (R.roseWord gs w)) (S1.intLoop (Z.pos n))
      ≡ R.roseWord gs (repeatWire n w)
  word-intLoop gs w zero = refl
  word-intLoop gs w (suc n) = cong-∙ (R.circleRec R.root (R.roseWord gs w)) (S1.intLoop (Z.pos n)) S1.loop
    ∙ cong (_∙ R.roseWord gs w) (word-intLoop gs w n)
    ∙ sym (R.eval-append (R.loopAt gs) (repeatWire n w) w)
    ∙ cong (R.roseWord gs) (sym (repeat-snoc n w))

  degree-word-loop : (gs : List ℕ) (w : P.Word) (n : ℕ)
    → cong (λ u → R.wordCircle gs w (R.mulC (Z.pos n) u)) Circle.hC
      ≡ R.roseWord gs (repeatWire n w)
  degree-word-loop gs w n =
    cong (λ z → cong (R.circleRec R.root (R.roseWord gs w)) (S1.intLoop z)) (Z.·IdR (Z.pos n))
    ∙ word-intLoop gs w n

boundaryProjection : (c : ShortCase) → R.FaceIx (S₀ c) → R.C → Γ
boundaryProjection c b u = R.wordCircle twoGenerators (Ch.kindWord (Ch.kind (bdAllAt c b)))
  (R.mulC (Z.pos (Ch.orbitLength (bdAllAt c b))) u)

abstract
  boundary-projection-loop : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → cong (projectGraph c) (boundaryLoop c b)
      ≡ cong (boundaryProjection c b) Circle.hC
  boundary-projection-loop c b = project-boundaryLoop c b
    ∙ cong (R.roseWord twoGenerators) (CheckedBoundary.input-checked c b)
    ∙ sym (degree-word-loop twoGenerators (Ch.kindWord (Ch.kind (bdAllAt c b))) (Ch.orbitLength (bdAllAt c b)))

  boundary-projection-S¹ : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : S1.S¹)
    → projectGraph c (R.circleRec (vertex (startSheet c b)) (boundaryLoop c b) u)
      ≡ boundaryProjection c b (Circle.circleToC u)
  boundary-projection-S¹ c b S1.base = refl
  boundary-projection-S¹ c b (S1.loop i) j = boundary-projection-loop c b j i

  liftedBoundary-projection : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
    → projectGraph c (liftedBoundary c b u) ≡ boundaryProjection c b u
  liftedBoundary-projection c b u = boundary-projection-S¹ c b (Circle.CToCircle u)
    ∙ cong (boundaryProjection c b) (Circle.circle-retraction u)

  liftedBoundary-projection-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → liftedBoundary-projection c b R.0C ≡ refl
  liftedBoundary-projection-base c b = sym (lUnit refl)
