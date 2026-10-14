{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerCubeAssembleComm where

-- Lower-dimensional wrapper of the prism calculation.
-- Geometric stages 1/2/3; all approximation windows remain length 6.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (assoc ; cong-∙∙ ; leftright)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (north)
open import Cubical.CW.Base using (CWskel ; realise ; CW↪)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; finCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.LowerCube as LowerCube
import DeloopS3.Bridge.DegreeSpan.LowerCubeClose as LowerCubeClose
import DeloopS3.Bridge.DegreeSpan.LowerCubeDirect as LowerCubeDirect

open FinSequenceMap

open import DeloopS3.Bridge.DegreeSpan.TopCubeAssembleComm using (mapped-left-whisker)

module AssembleComm (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = LowerCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt
  module D = LowerCubeDirect.Direct Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
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

    module G = A.G u∞ v∞ w∞ hL∞ hR∞ d

    private
      Z : Type
      Z = C.Z u∞ v∞ w∞ hL∞ hR∞ d

      u₆ : finCellMap 6 W.Xs W.Xt
      u₆ = W.u u∞ v∞ w∞ hL∞ hR∞ d

    private
      module _ (x : fst W.Xs 1) where
        low : Path Z north north
        low = cong (T.prismCollapse 1 ∘ CW↪ W.Yt 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)

        bareLow : Path Z north north
        bareLow = cong (T.prismCollapse 1)
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)

        upper : Path Z north north
        upper = cong (T.prismCollapse 1)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x))

        normalizedLow : Path Z north north
        normalizedLow = T.normalizedMeridian 1
          (inr (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x)))

        high : Path Z north north
        high = T.normalizedMeridian 1
          (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)))

        boundary : I → Type
        boundary j = Path (fst W.Yt 3)
          (inl (A.aStep u∞ v∞ w∞ hL∞ hR∞ d x j))
          (inr (A.bStep u∞ v∞ w∞ hL∞ hR∞ d x j))

        p : Path (boundary i0)
          (cong (CW↪ W.Yt 2)
            (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)
        p = cong-∙∙ (CW↪ W.Yt 2)
          (cong (W.leftYt 1) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))
          (push (fmap u₆ (1 , tt) x))
          (sym (cong (W.rightYt 1)
            (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)))

        q : PathP boundary
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x))
        q = A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x

        F : (j : I) → boundary j → Path Z north north
        F j pth = cong (T.prismCollapse 1) pth

        cp : Path (Path Z north north) low bareLow
        cp = cong (cong (T.prismCollapse 1)) p

        bare : Path (Path Z north north) bareLow upper
        bare j k = T.prismCollapse 1 (q j k)

        actual : Path (Path Z north north) low upper
        actual j k = T.prismCollapse 1
          (C.c₂ u∞ v∞ w∞ hL∞ hR∞ d (push x k) j)

        g0 : Path (Path Z north north) bareLow normalizedLow
        g0 = G.normalize (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))
          (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
          (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x)

        g1 : Path (Path Z north north) upper high
        g1 = G.normalize (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x))
          (A.l1 u∞ v∞ w∞ hL∞ hR∞ d x)
          (A.r1 u∞ v∞ w∞ hL∞ hR∞ d x)

        ustep : Path (Path Z north north) normalizedLow high
        ustep = D.targetStep u∞ v∞ w∞ hL∞ hR∞ d x

    abstract
      collapsed-comm-agreement : A.CollapsedCommAgreement u∞ v∞ w∞ hL∞ hR∞ d
      collapsed-comm-agreement x =
        cong (λ sq j k → T.prismCollapse 1 (sq j k))
          (W.S_total-unfold u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)
        ∙ mapped-left-whisker (boundary x) (Path Z north north) (F x)
            {a0 = cong (CW↪ W.Yt 2)
              (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)}
            {a0' = A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0}
            {a1 = W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) (CW↪ W.Xs 1 x)}
            (p x) (q x)

      actual-overlap-pasting : (x : fst W.Xs 1)
        → Path
            (Path (Path Z north north)
              (cong (T.prismCollapse 1 ∘ CW↪ W.Yt 2)
                (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))
              (T.normalizedMeridian 1
                (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)))))
            ((cp x ∙ g0 x) ∙ ustep x)
            (actual x ∙ g1 x)
      actual-overlap-pasting x =
        sym (assoc (cp x) (g0 x) (ustep x))
        ∙ cong (cp x ∙_) (D.bare-overlap-pasting u∞ v∞ w∞ hL∞ hR∞ d x)
        ∙ assoc (cp x) (bare x) (g1 x)
        ∙ cong (_∙ g1 x) (sym (collapsed-comm-agreement x))
