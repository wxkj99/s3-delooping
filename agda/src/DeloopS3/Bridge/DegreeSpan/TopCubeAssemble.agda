{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeAssemble where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Pushout using (inr ; push)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.CW.Base using (CWskel ; realise ; cofibCW ; CW↪)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; finCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopCubeClose as TopCubeClose
import DeloopS3.Bridge.DegreeSpan.TopCubeDirect as TopCubeDirect
open import DeloopS3.Bridge.DegreeSpan.TopCubeAssembleAlgebra
  using (pasting-square ; exact-unit-cube)
import DeloopS3.Bridge.DegreeSpan.TopCubeAssembleLower as TopCubeAssembleLower
import DeloopS3.Bridge.DegreeSpan.TopCubeAssembleComm as TopCubeAssembleComm

open FinSequenceMap

module Assemble (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = TopCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt
  module D = TopCubeDirect.Direct Os Ls Rs Ot Lt Rt fs gs ft gt
  module Lower = TopCubeAssembleLower.AssembleLower
    Os Ls Rs Ot Lt Rt fs gs ft gt
  module Comm = TopCubeAssembleComm.AssembleComm
    Os Ls Rs Ot Lt Rt fs gs ft gt
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

    private
      Z : Type
      Z = C.Z u∞ v∞ w∞ hL∞ hR∞ d

      u₆ : finCellMap 6 W.Xs W.Xt
      u₆ = C.u₆ u∞ v∞ w∞ hL∞ hR∞ d

      Q₂u : cofibCW 2 W.Xs → cofibCW 2 W.Xt
      Q₂u = C.Q₂u u∞ v∞ w∞ hL∞ hR∞ d

      s : Susp (cofibCW 2 W.Xs) → Z
      s = C.s u∞ v∞ w∞ hL∞ hR∞ d

    module N = D.N u∞ v∞ w∞ hL∞ hR∞ d
    module G = A.G u∞ v∞ w∞ hL∞ hR∞ d

    abstract
      meridian-face-agreement : (z : cofibCW 2 W.Xs)
        → Path
            (Path (Path Z north north)
              (cong s (S.normalizedMeridian 2 z))
              (T.normalizedMeridian 2 (Q₂u z)))
            (N.e z)
            (C.normalizedMeridian-natural u∞ v∞ w∞ hL∞ hR∞ d z)
      meridian-face-agreement z =
        sym (C.normalizedMeridian-natural-unfold u∞ v∞ w∞ hL∞ hR∞ d z)

      upper-normalization-agreement
        : A.UpperNormalizationAgreement u∞ v∞ w∞ hL∞ hR∞ d
      upper-normalization-agreement x =
        C.collapse-three-piece-unfold u∞ v∞ w∞ hL∞ hR∞ d x

      H₀-seam-normal : (x : fst W.Xs 3)
        → Path
            (Path (Path Z north north)
              (cong (T.prismCollapse 2)
                (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x))
              (cong s (S.normalizedMeridian 2 (inr x))))
            (λ t k → C.H₀ u∞ v∞ w∞ hL∞ hR∞ d (push x k) t)
            (G.normalize (fmap u₆ (3 , tt) x)
              (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)
              (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)
              ∙ sym (N.e (inr x)))
      H₀-seam-normal x =
        cong₂ _∙_ (upper-normalization-agreement x)
          (cong sym
            (C.normalizedMeridian-natural-unfold u∞ v∞ w∞ hL∞ hR∞ d (inr x)))

      overlap-null-cube-actual-face : (x : fst W.Xs 2)
        → Square {A = Path Z north north}
            (D.sourceNull u∞ v∞ w∞ hL∞ hR∞ d x)
            (D.targetExpanded u∞ v∞ w∞ hL∞ hR∞ d x)
            refl
            (C.normalizedMeridian-natural u∞ v∞ w∞ hL∞ hR∞ d
              (inr (CW↪ W.Xs 2 x)))
      overlap-null-cube-actual-face x =
        subst
          (λ e → Square {A = Path Z north north}
            (D.sourceNull u∞ v∞ w∞ hL∞ hR∞ d x)
            (D.targetExpanded u∞ v∞ w∞ hL∞ hR∞ d x) refl e)
          (meridian-face-agreement (inr (CW↪ W.Xs 2 x)))
          (D.overlap-null-cube u∞ v∞ w∞ hL∞ hR∞ d x)

      collapsed-comm-agreement
        : A.CollapsedCommAgreement u∞ v∞ w∞ hL∞ hR∞ d
      collapsed-comm-agreement =
        Comm.collapsed-comm-agreement u∞ v∞ w∞ hL∞ hR∞ d

    private
      module _ (x : fst W.Xs 2) where
        L : Type
        L = Path Z north north

        low : L
        low = Lower.low u∞ v∞ w∞ hL∞ hR∞ d x

        high : L
        high = cong (T.prismCollapse 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x))

        src : L
        src = cong s (S.normalizedMeridian 2 (inr (CW↪ W.Xs 2 x)))

        m0 : L
        m0 = Lower.m u∞ v∞ w∞ hL∞ hR∞ d x

        m1 : L
        m1 = T.normalizedMeridian 2
          (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))

        v : Path L refl low
        v = Lower.v u∞ v∞ w∞ hL∞ hR∞ d x

        c : Path L low high
        c j k = T.prismCollapse 2 (C.c₃ u∞ v∞ w∞ hL∞ hR∞ d (push x k) j)

        g0 : Path L low m0
        g0 = Lower.cp u∞ v∞ w∞ hL∞ hR∞ d x
          ∙ Lower.g0 u∞ v∞ w∞ hL∞ hR∞ d x

        g1 : Path L high m1
        g1 = G.normalize (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))
          (A.l1 u∞ v∞ w∞ hL∞ hR∞ d x)
          (A.r1 u∞ v∞ w∞ hL∞ hR∞ d x)

        u : Path L m0 m1
        u = D.targetStep u∞ v∞ w∞ hL∞ hR∞ d x

        n : Path L refl m0
        n = Lower.n u∞ v∞ w∞ hL∞ hR∞ d x

        b : Path L refl src
        b = D.sourceNull u∞ v∞ w∞ hL∞ hR∞ d x

        e : Path L src m1
        e = N.e (inr (CW↪ W.Xs 2 x))

        h : Path L high src
        h t k = C.H₀ u∞ v∞ w∞ hL∞ hR∞ d (CW↪ W.Ys 3 (push x k)) t

        Qnormal : Square {A = L} (v ∙ c) b refl (g1 ∙ sym e)
        Qnormal = pasting-square {B = L} v c g0 g1 u n b e
          (Lower.lower-null-pasting u∞ v∞ w∞ hL∞ hR∞ d x)
          (Comm.actual-overlap-pasting u∞ v∞ w∞ hL∞ hR∞ d x)
          (D.overlap-null-cube u∞ v∞ w∞ hL∞ hR∞ d x)

        Qactual : Square {A = L} (v ∙ c) b refl h
        Qactual = subst (λ hh → Square {A = L} (v ∙ c) b refl hh)
          (sym (H₀-seam-normal (CW↪ W.Xs 2 x))) Qnormal

    abstract
      direct-seam-residual : D.DirectSeamResidual u∞ v∞ w∞ hL∞ hR∞ d
      direct-seam-residual x =
        exact-unit-cube Z north (v x) (c x) (b x) (h x) (Qactual x)
