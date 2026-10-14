{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopRNaturalUnconditional where

open import Cubical.Foundations.Prelude
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopRNaturalFinal as TopRNaturalFinal
import DeloopS3.Bridge.DegreeSpan.TopCubeAssemble as TopCubeAssemble

-- Unconditional means there is no seam cube premise; finite span data remains.
module TotalWindowNaturality (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module Final = TopRNaturalFinal.TotalWindowNaturality
    Os Ls Rs Ot Lt Rt fs gs ft gt
  module Assembly = TopCubeAssemble.Assemble
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

    abstract
      top-R-natural-unconditional : Final.TopRNaturality u∞ v∞ w∞ hL∞ hR∞ d
      top-R-natural-unconditional =
        Final.top-R-natural-from-direct-residual u∞ v∞ w∞ hL∞ hR∞ d
          (Assembly.direct-seam-residual u∞ v∞ w∞ hL∞ hR∞ d)
