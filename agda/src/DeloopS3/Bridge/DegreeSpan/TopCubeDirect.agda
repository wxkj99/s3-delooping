{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeDirect where

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
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopCubeClose as TopCubeClose
open import DeloopS3.Bridge.DegreeSpan.TopCubeDirectOverlap
  using (module NormalizedNull)

open FinSequenceMap

-- Overlap-only naturality, used by TopCubeAssemble to construct the seam cube.
module Direct (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = TopCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt
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

    Q₂u : cofibCW 2 W.Xs → cofibCW 2 W.Xt
    Q₂u = C.Q₂u u∞ v∞ w∞ hL∞ hR∞ d

    s : Susp (cofibCW 2 W.Xs) → Z
    s = C.s u∞ v∞ w∞ hL∞ hR∞ d

    F₃ : fst W.Ys 3 → fst W.Yt 3
    F₃ = C.F₃ u∞ v∞ w∞ hL∞ hR∞ d

    c₃ : (y : fst W.Ys 3)
      → Path (fst W.Yt 4)
          (CW↪ W.Yt 3 (F₃ y))
          (C.F₄ u∞ v∞ w∞ hL∞ hR∞ d (CW↪ W.Ys 3 y))
    c₃ = C.c₃ u∞ v∞ w∞ hL∞ hR∞ d

    H₀ : (z : fst W.Ys 4)
      → Path Z
          (T.prismCollapse 2 (C.F₄ u∞ v∞ w∞ hL∞ hR∞ d z))
          (s (S.prismCollapse 2 z))
    H₀ = C.H₀ u∞ v∞ w∞ hL∞ hR∞ d

    module N = NormalizedNull (cofibCW 2 W.Xs) (cofibCW 2 W.Xt)
      (inl tt) Q₂u
    module G = A.G u∞ v∞ w∞ hL∞ hR∞ d

    uStep : (x : fst W.Xs 2)
      → CW↪ W.Xt 2 (fmap u₆ (2 , tt) x)
      ≡ fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)
    uStep x = fcomm u₆ (2 , tt) x

    sourceNull : (x : fst W.Xs 2)
      → Path (Path Z north north) refl
          (cong s (S.normalizedMeridian 2 (inr (CW↪ W.Xs 2 x))))
    sourceNull x j k = s (S.prismNull 2 (push x k) j)

    targetStep : (x : fst W.Xs 2)
      → Path (Path Z north north)
          (T.normalizedMeridian 2 (inr (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))))
          (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))))
    targetStep x = cong (T.normalizedMeridian 2 ∘ inr) (uStep x)

    targetExpanded : (x : fst W.Xs 2)
      → Path (Path Z north north) refl
          (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))))
    targetExpanded x = T.prismCollapse-seam 2 (fmap u₆ (2 , tt) x) ∙ targetStep x

    abstract
      source-null-normal : (x : fst W.Xs 2)
        → Path
            (Path (Path Z north north) refl
              (cong s (S.normalizedMeridian 2 (inr (CW↪ W.Xs 2 x)))))
            (sourceNull x)
            (cong (cong s) (N.nullS (push x)))
      source-null-normal x =
        cong (cong (cong s)) (C.SourceNull.null-on-seam 2 x)

      target-null-normal : (y : fst W.Xt 2)
        → Path
            (Path (Path Z north north) refl
              (T.normalizedMeridian 2 (inr (CW↪ W.Xt 2 y))))
            (T.prismCollapse-seam 2 y)
            (N.targetBase ∙ cong (T.normalizedMeridian 2) (push y))
      target-null-normal y =
        T.prismCollapse-seam-unfold 2 y
        ∙ cong (λ c → r ∙ sym c) (C.TargetNull.seam-correction-null 2 y)
        ∙ sym (rUnit r)
        where
        r : Path (Path Z north north) refl
          (T.normalizedMeridian 2 (inr (CW↪ W.Xt 2 y)))
        r = N.targetBase ∙ cong (T.normalizedMeridian 2) (push y)

      target-null-expansion : (x : fst W.Xs 2)
        → Path
            (Path (Path Z north north) refl
              (T.normalizedMeridian 2
                (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))))
            (N.nullT (push x))
            (targetExpanded x)
      target-null-expansion x =
        cong (N.targetBase ∙_)
          (C.overlap-meridian-push-expanded u∞ v∞ w∞ hL∞ hR∞ d x)
        ∙ assoc N.targetBase
            (cong (T.normalizedMeridian 2) (push (fmap u₆ (2 , tt) x)))
            (targetStep x)
        ∙ cong (λ p → p ∙ targetStep x)
            (sym (target-null-normal (fmap u₆ (2 , tt) x)))

      -- Both nulls use the actual exported source/target witnesses.
      -- The meridian face is the explicit canonical N.e, NOT the abstract
      -- C.normalizedMeridian-natural used in H₀.
      overlap-null-cube : (x : fst W.Xs 2)
        → Square {A = Path Z north north}
            (sourceNull x) (targetExpanded x) refl
            (N.e (inr (CW↪ W.Xs 2 x)))
      overlap-null-cube x =
        source-null-normal x ◁ N.null-square (push x) ▷ target-null-expansion x

      -- Pasting for the bare cube only; no identification with S_total.
      bare-overlap-pasting : (x : fst W.Xs 2) →
        let
          low : Path Z north north
          low = λ k → T.prismCollapse 2
            (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0 k)
          high : Path Z north north
          high = T.normalizedMeridian 2
            (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))
        in Path (Path (Path Z north north) low high)
          (G.normalize (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))
            (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
            (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x)
            ∙ targetStep x)
          ((λ j k → T.prismCollapse 2
              (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x j k))
            ∙ G.normalize (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))
              (A.l1 u∞ v∞ w∞ hL∞ hR∞ d x)
              (A.r1 u∞ v∞ w∞ hL∞ hR∞ d x))
      bare-overlap-pasting x =
        Square→compPath (A.bare-comm-normalizes u∞ v∞ w∞ hL∞ hR∞ d x)

    -- Comparison types for total-map commutation and upper normalization.
    -- TopCubeAssemble supplies these comparisons before pasting the seam cube.
    CollapsedCommAgreement : Type
    CollapsedCommAgreement = A.CollapsedCommAgreement u∞ v∞ w∞ hL∞ hR∞ d

    UpperNormalizationAgreement : Type
    UpperNormalizationAgreement = A.UpperNormalizationAgreement u∞ v∞ w∞ hL∞ hR∞ d

    -- The seam cube uses the actual H₀ face, rather than the canonical meridian face.
    -- For seam coordinate k, naturality coordinate t, path coordinate j,
    -- all six faces are fixed exactly as follows:
    -- t=0: (T.prismNull 2 (F₃ (push x k))
    --         ∙ cong (T.prismCollapse 2) (c₃ (push x k))) j
    -- t=1: cong s (S.prismNull 2 (push x k)) j
    -- j=0: north
    -- j=1: H₀ (CW↪ W.Ys 3 (push x k)) t
    -- k=0: sym (rUnit (refl {x = north})) t j
    -- k=1: sym (rUnit (refl {x = north})) t j
    DirectSeamResidual : Type
    DirectSeamResidual = (x : fst W.Xs 2)
      → PathP
          (λ k → Square {A = Z}
            (T.prismNull 2 (F₃ (push x k))
              ∙ cong (T.prismCollapse 2) (c₃ (push x k)))
            (cong s (S.prismNull 2 (push x k)))
            refl
            (H₀ (CW↪ W.Ys 3 (push x k))))
          (sym (rUnit (refl {x = north})))
          (sym (rUnit (refl {x = north})))

    abstract
      -- Convert the specified seam cube to full retraction naturality.
      remaining-seam-from-direct : DirectSeamResidual
        → C.RemainingSeamCube u∞ v∞ w∞ hL∞ hR∞ d
      remaining-seam-from-direct = λ K → K

      cube-from-direct : DirectSeamResidual → C.Cube u∞ v∞ w∞ hL∞ hR∞ d
      cube-from-direct K (inl b) = C.vertexL u∞ v∞ w∞ hL∞ hR∞ d b
      cube-from-direct K (inr c) = C.vertexR u∞ v∞ w∞ hL∞ hR∞ d c
      cube-from-direct K (push x k) = K x k

      prismRet-natural-from-direct : DirectSeamResidual
        → Path (cofibCW 3 W.Ys → Z)
            (T.prismRet 2 ∘ C.Q₃Φ u∞ v∞ w∞ hL∞ hR∞ d)
            (s ∘ S.prismRet 2)
      prismRet-natural-from-direct =
        C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d
