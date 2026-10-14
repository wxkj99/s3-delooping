{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerCubeDirect where

-- Lower-dimensional wrapper of the prism calculation.
-- Geometric stages 1/2/3; all approximation windows remain length 6.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Foundations.GroupoidLaws using (assoc ; rUnit)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.CW.Base using (CWskel ; realise ; cofibCW ; CW↪)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; finCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.LowerCube as LowerCube
import DeloopS3.Bridge.DegreeSpan.LowerCubeClose as LowerCubeClose
open import DeloopS3.Bridge.DegreeSpan.TopCubeDirectOverlap
  using (module NormalizedNull)

open FinSequenceMap

module Direct (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = LowerCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
  module S = C.S
  module T = C.T

  module _
    (u∞ : realise W.Xs → realise W.Xt)
    (v∞ : realise W.Bs → realise W.Bt)
    (w∞ : realise W.Cs → realise W.Ct)
    (hL∞ : (x : realise W.Xs)
      → v∞ (realiseCellMap {C = W.Xs} {D = W.Bs} W.S.f x)
      ≡ realiseCellMap {C = W.Xt} {D = W.Bt} W.T.f (u∞ x))
    (hR∞ : (x : realise W.Xs)
      → w∞ (realiseCellMap {C = W.Xs} {D = W.Cs} W.S.g x)
      ≡ realiseCellMap {C = W.Xt} {D = W.Ct} W.T.g (u∞ x))
    (d : W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where

    Z : Type
    Z = C.Z u∞ v∞ w∞ hL∞ hR∞ d

    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = C.u₆ u∞ v∞ w∞ hL∞ hR∞ d

    Q₁u : cofibCW 1 W.Xs → cofibCW 1 W.Xt
    Q₁u = C.Q₁u u∞ v∞ w∞ hL∞ hR∞ d

    s : Susp (cofibCW 1 W.Xs) → Z
    s = C.s u∞ v∞ w∞ hL∞ hR∞ d

    F₂ : fst W.Ys 2 → fst W.Yt 2
    F₂ = C.F₂ u∞ v∞ w∞ hL∞ hR∞ d

    c₂ : (y : fst W.Ys 2)
      → Path (fst W.Yt 3)
          (CW↪ W.Yt 2 (F₂ y))
          (C.F₃ u∞ v∞ w∞ hL∞ hR∞ d (CW↪ W.Ys 2 y))
    c₂ = C.c₂ u∞ v∞ w∞ hL∞ hR∞ d

    H₀ : (z : fst W.Ys 3)
      → Path Z
          (T.prismCollapse 1 (C.F₃ u∞ v∞ w∞ hL∞ hR∞ d z))
          (s (S.prismCollapse 1 z))
    H₀ = C.H₀ u∞ v∞ w∞ hL∞ hR∞ d

    module N = NormalizedNull (cofibCW 1 W.Xs) (cofibCW 1 W.Xt)
      (inl tt) Q₁u
    module G = A.G u∞ v∞ w∞ hL∞ hR∞ d

    uStep : (x : fst W.Xs 1)
      → CW↪ W.Xt 1 (fmap u₆ (1 , tt) x)
      ≡ fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)
    uStep x = fcomm u₆ (1 , tt) x

    sourceNull : (x : fst W.Xs 1)
      → Path (Path Z north north) refl
          (cong s (S.normalizedMeridian 1 (inr (CW↪ W.Xs 1 x))))
    sourceNull x j k = s (S.prismNull 1 (push x k) j)

    targetStep : (x : fst W.Xs 1)
      → Path (Path Z north north)
          (T.normalizedMeridian 1 (inr (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))))
          (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))))
    targetStep x = cong (T.normalizedMeridian 1 ∘ inr) (uStep x)

    targetExpanded : (x : fst W.Xs 1)
      → Path (Path Z north north) refl
          (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))))
    targetExpanded x = T.prismCollapse-seam 1 (fmap u₆ (1 , tt) x) ∙ targetStep x

    abstract
      source-null-normal : (x : fst W.Xs 1)
        → Path
            (Path (Path Z north north) refl
              (cong s (S.normalizedMeridian 1 (inr (CW↪ W.Xs 1 x)))))
            (sourceNull x)
            (cong (cong s) (N.nullS (push x)))
      source-null-normal x =
        cong (cong (cong s)) (C.SourceNull.null-on-seam 1 x)

      target-null-normal : (y : fst W.Xt 1)
        → Path
            (Path (Path Z north north) refl
              (T.normalizedMeridian 1 (inr (CW↪ W.Xt 1 y))))
            (T.prismCollapse-seam 1 y)
            (N.targetBase ∙ cong (T.normalizedMeridian 1) (push y))
      target-null-normal y =
        T.prismCollapse-seam-unfold 1 y
        ∙ cong (λ c → r ∙ sym c) (C.TargetNull.seam-correction-null 1 y)
        ∙ sym (rUnit r)
        where
        r : Path (Path Z north north) refl
          (T.normalizedMeridian 1 (inr (CW↪ W.Xt 1 y)))
        r = N.targetBase ∙ cong (T.normalizedMeridian 1) (push y)

      target-null-expansion : (x : fst W.Xs 1)
        → Path
            (Path (Path Z north north) refl
              (T.normalizedMeridian 1
                (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)))))
            (N.nullT (push x))
            (targetExpanded x)
      target-null-expansion x =
        cong (N.targetBase ∙_)
          (C.overlap-meridian-push-expanded u∞ v∞ w∞ hL∞ hR∞ d x)
        ∙ assoc N.targetBase
            (cong (T.normalizedMeridian 1) (push (fmap u₆ (1 , tt) x)))
            (targetStep x)
        ∙ cong (λ p → p ∙ targetStep x)
            (sym (target-null-normal (fmap u₆ (1 , tt) x)))

      overlap-null-cube : (x : fst W.Xs 1)
        → Square {A = Path Z north north}
            (sourceNull x) (targetExpanded x) refl
            (N.e (inr (CW↪ W.Xs 1 x)))
      overlap-null-cube x =
        source-null-normal x ◁ N.null-square (push x) ▷ target-null-expansion x

      bare-overlap-pasting : (x : fst W.Xs 1) →
        let
          low : Path Z north north
          low = λ k → T.prismCollapse 1
            (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0 k)
          high : Path Z north north
          high = T.normalizedMeridian 1
            (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)))
        in Path (Path (Path Z north north) low high)
          (G.normalize (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))
            (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
            (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x)
            ∙ targetStep x)
          ((λ j k → T.prismCollapse 1
              (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x j k))
            ∙ G.normalize (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))
              (A.l1 u∞ v∞ w∞ hL∞ hR∞ d x)
              (A.r1 u∞ v∞ w∞ hL∞ hR∞ d x))
      bare-overlap-pasting x =
        Square→compPath (A.bare-comm-normalizes u∞ v∞ w∞ hL∞ hR∞ d x)

    CollapsedCommAgreement : Type
    CollapsedCommAgreement = A.CollapsedCommAgreement u∞ v∞ w∞ hL∞ hR∞ d

    UpperNormalizationAgreement : Type
    UpperNormalizationAgreement = A.UpperNormalizationAgreement u∞ v∞ w∞ hL∞ hR∞ d

    DirectSeamResidual : Type
    DirectSeamResidual = (x : fst W.Xs 1)
      → PathP
          (λ k → Square {A = Z}
            (T.prismNull 1 (F₂ (push x k))
              ∙ cong (T.prismCollapse 1) (c₂ (push x k)))
            (cong s (S.prismNull 1 (push x k)))
            refl
            (H₀ (CW↪ W.Ys 2 (push x k))))
          (sym (rUnit (refl {x = north})))
          (sym (rUnit (refl {x = north})))

    abstract
      remaining-seam-from-direct : DirectSeamResidual
        → C.RemainingSeamCube u∞ v∞ w∞ hL∞ hR∞ d
      remaining-seam-from-direct = λ K → K

      cube-from-direct : DirectSeamResidual → C.Cube u∞ v∞ w∞ hL∞ hR∞ d
      cube-from-direct K (inl b) = C.vertexL u∞ v∞ w∞ hL∞ hR∞ d b
      cube-from-direct K (inr c) = C.vertexR u∞ v∞ w∞ hL∞ hR∞ d c
      cube-from-direct K (push x k) = K x k

      prismRet-natural-from-direct : DirectSeamResidual
        → Path (cofibCW 2 W.Ys → Z)
            (T.prismRet 1 ∘ C.Q₂Φ u∞ v∞ w∞ hL∞ hR∞ d)
            (s ∘ S.prismRet 1)
      prismRet-natural-from-direct =
        C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d
