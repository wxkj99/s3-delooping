{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopRNaturalFinal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.Map using
  (cellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopCubeDirect as TopCubeDirect
import DeloopS3.Bridge.DegreeSpan.TopCubeFinalDegree as TopCubeFinalDegree

-- Top-R naturality from finite span data and a direct seam cube.
-- TopRNaturalUnconditional supplies the cube via TopCubeAssemble; no global cellMaps are used.
module TotalWindowNaturality (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module Direct = TopCubeDirect.Direct Os Ls Rs Ot Lt Rt fs gs ft gt
  module Degree = TopCubeFinalDegree.TotalWindowDegree
    Os Ls Rs Ot Lt Rt fs gs ft gt

  module _
    (u∞ : realise C.W.Xs → realise C.W.Xt)
    (v∞ : realise C.W.Bs → realise C.W.Bt)
    (w∞ : realise C.W.Cs → realise C.W.Ct)
    (hL∞ : (x : realise C.W.Xs)
      → v∞ (realiseCellMap {C = C.W.Xs} {D = C.W.Bs} C.W.S.f x)
      ≡ realiseCellMap {C = C.W.Xt} {D = C.W.Bt} C.W.T.f (u∞ x))
    (hR∞ : (x : realise C.W.Xs)
      → w∞ (realiseCellMap {C = C.W.Xs} {D = C.W.Cs} C.W.S.g x)
      ≡ realiseCellMap {C = C.W.Xt} {D = C.W.Ct} C.W.T.g (u∞ x))
    (d : C.W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where

    TopRNaturality : Type
    TopRNaturality =
      compGroupHom
        (prefunctoriality.chainFunct 6
          (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d) (3 , tt)) (C.T.R 2)
      ≡ compGroupHom (C.S.R 2)
        (prefunctoriality.chainFunct 6
          (C.u₆ u∞ v∞ w∞ hL∞ hR∞ d) (2 , tt))

    abstract
      top-R-natural-from-direct-residual
        : Direct.DirectSeamResidual u∞ v∞ w∞ hL∞ hR∞ d
        → TopRNaturality
      top-R-natural-from-direct-residual K =
        Degree.finite-top-R-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d
          (Direct.remaining-seam-from-direct u∞ v∞ w∞ hL∞ hR∞ d K)
