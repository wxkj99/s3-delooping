{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerCubeClose where

-- Lower-dimensional wrapper of the prism calculation.
-- Geometric stages 1/2/3; all approximation windows remain length 6.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.HITs.Pushout.Base using (Pushout ; inl ; inr ; push)
open import DeloopS3.Bridge.DegreeSpan.TopCubeClose using (module CollapsedThreePiece)

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Susp using (north)
open import Cubical.CW.Base using (CWskel ; realise ; cofibCW ; CW↪)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; finCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.LowerCube as LowerCube

open FinSequenceMap

module ActualWindow (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
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

    module G = CollapsedThreePiece
      (fst W.Xt 2) (fst W.Bt 3) (fst W.Ct 3) Z
      (λ x → inl (SequenceMap.map W.T.f 2 x))
      (λ x → inl (SequenceMap.map W.T.g 2 x))
      north (λ x → T.normalizedMeridian 1 (inr x))

    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = W.u u∞ v∞ w∞ hL∞ hR∞ d

    v₆ : finCellMap 6 W.Bs W.Bt
    v₆ = W.v u∞ v∞ w∞ hL∞ hR∞ d

    w₆ : finCellMap 6 W.Cs W.Ct
    w₆ = W.w u∞ v∞ w∞ hL∞ hR∞ d

    uStep : (x : fst W.Xs 1)
      → Path (fst W.Xt 2)
          (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))
          (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))
    uStep x = fcomm u₆ (1 , tt) x

    aStep : (x : fst W.Xs 1)
      → Path (fst W.Bt 3)
          (CW↪ W.Bt 2 (fmap v₆ (2 , tt) (inl (SequenceMap.map W.S.f 1 x))))
          (fmap v₆ (3 , tt) (CW↪ W.Bs 2 (inl (SequenceMap.map W.S.f 1 x))))
    aStep x = fcomm v₆ (2 , tt) (inl (SequenceMap.map W.S.f 1 x))

    bStep : (x : fst W.Xs 1)
      → Path (fst W.Ct 3)
          (CW↪ W.Ct 2 (fmap w₆ (2 , tt) (inl (SequenceMap.map W.S.g 1 x))))
          (fmap w₆ (3 , tt) (CW↪ W.Cs 2 (inl (SequenceMap.map W.S.g 1 x))))
    bStep x = fcomm w₆ (2 , tt) (inl (SequenceMap.map W.S.g 1 x))

    l0 : (x : fst W.Xs 1)
      → Path (fst W.Bt 3)
          (CW↪ W.Bt 2 (fmap v₆ (2 , tt) (inl (SequenceMap.map W.S.f 1 x))))
          (inl (SequenceMap.map W.T.f 2 (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))))
    l0 x = cong (CW↪ W.Bt 2) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)

    l1 : (x : fst W.Xs 1)
      → Path (fst W.Bt 3)
          (fmap v₆ (3 , tt) (CW↪ W.Bs 2 (inl (SequenceMap.map W.S.f 1 x))))
          (inl (SequenceMap.map W.T.f 2 (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))))
    l1 x = W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x)

    r0 : (x : fst W.Xs 1)
      → Path (fst W.Ct 3)
          (CW↪ W.Ct 2 (fmap w₆ (2 , tt) (inl (SequenceMap.map W.S.g 1 x))))
          (inl (SequenceMap.map W.T.g 2 (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))))
    r0 x = cong (CW↪ W.Ct 2) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)

    r1 : (x : fst W.Xs 1)
      → Path (fst W.Ct 3)
          (fmap w₆ (3 , tt) (CW↪ W.Cs 2 (inl (SequenceMap.map W.S.g 1 x))))
          (inl (SequenceMap.map W.T.g 2 (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))))
    r1 x = W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x)

    HL : (x : fst W.Xs 1)
      → Square {A = fst W.Bt 3} (l0 x) (l1 x) (aStep x)
          (cong (λ z → inl (SequenceMap.map W.T.f 2 z)) (uStep x))
    HL x = W.hatL-coh u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x

    HR : (x : fst W.Xs 1)
      → Square {A = fst W.Ct 3} (r0 x) (r1 x) (bStep x)
          (cong (λ z → inl (SequenceMap.map W.T.g 2 z)) (uStep x))
    HR x = W.hatR-coh u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x

    bare-comm : (x : fst W.Xs 1)
      → Square {A = fst W.Yt 3}
          (G.three (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x)) (l0 x) (r0 x))
          (G.three (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)) (l1 x) (r1 x))
          (cong inl (aStep x)) (cong inr (bStep x))
    bare-comm x = G.three-square (aStep x) (bStep x) (uStep x)
      (l0 x) (l1 x) (r0 x) (r1 x) (HL x) (HR x)

    abstract
      bare-comm-normalizes : (x : fst W.Xs 1)
        → Square {A = Path Z north north}
            (λ j k → T.prismCollapse 1 (bare-comm x j k))
            (cong (λ z → T.normalizedMeridian 1 (inr z)) (uStep x))
            (G.normalize (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x)) (l0 x) (r0 x))
            (G.normalize (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)) (l1 x) (r1 x))
      bare-comm-normalizes x = G.normalize-square (aStep x) (bStep x) (uStep x)
        (l0 x) (l1 x) (r0 x) (r1 x) (HL x) (HR x)

    CollapsedCommAgreement : Type
    CollapsedCommAgreement = (x : fst W.Xs 1) →
      let
        low : Path Z north north
        low = cong (T.prismCollapse 1 ∘ CW↪ W.Yt 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)
        high : Path Z north north
        high = cong (T.prismCollapse 1)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x))
        actual : Path (Path Z north north) low high
        actual = λ j k → T.prismCollapse 1
          (C.c₂ u∞ v∞ w∞ hL∞ hR∞ d (push x k) j)
        raw : Path (Path Z north north) low high
        raw = cong (cong (T.prismCollapse 1))
          (cong-∙∙ (CW↪ W.Yt 2)
            (cong (W.leftYt 1) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))
            (push (fmap u₆ (1 , tt) x))
            (sym (cong (W.rightYt 1) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))))
          ∙ (λ j k → T.prismCollapse 1 (bare-comm x j k))
      in Path (Path (Path Z north north) low high) actual raw

    UpperNormalizationAgreement : Type
    UpperNormalizationAgreement = (x : fst W.Xs 2) →
      let
        low : Path Z north north
        low = cong (T.prismCollapse 1)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)
        high : Path Z north north
        high = T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) x))
        actual : Path (Path Z north north) low high
        actual = C.collapse-three-piece u∞ v∞ w∞ hL∞ hR∞ d x
        normalized : Path (Path Z north north) low high
        normalized = G.normalize (fmap u₆ (2 , tt) x)
          (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)
          (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)
      in Path (Path (Path Z north north) low high) actual normalized

    RemainingSeamCube : Type
    RemainingSeamCube = (x : fst W.Xs 1)
      → PathP (λ k → C.CubeAt u∞ v∞ w∞ hL∞ hR∞ d (push x k))
          (C.vertexL u∞ v∞ w∞ hL∞ hR∞ d (inl (SequenceMap.map W.S.f 1 x)))
          (C.vertexR u∞ v∞ w∞ hL∞ hR∞ d (inl (SequenceMap.map W.S.g 1 x)))

    prismRet-natural-from-residual : RemainingSeamCube
      → Path (cofibCW 2 W.Ys → Z)
          (T.prismRet 1 ∘ C.Q₂Φ u∞ v∞ w∞ hL∞ hR∞ d)
          (C.s u∞ v∞ w∞ hL∞ hR∞ d ∘ S.prismRet 1)
    prismRet-natural-from-residual = C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d

