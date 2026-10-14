{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerCubeAssembleLower where

-- Lower-dimensional wrapper of the prism calculation.
-- Geometric stages 1/2/3; all approximation windows remain length 6.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Foundations.GroupoidLaws
  using (cong-∙∙ ; cong-∙∙-filler ; rUnit ; lUnit)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.Sequence using (SequenceMap)
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

open import DeloopS3.Bridge.DegreeSpan.TopCubeAssembleLower using (cancel-square)

module AssembleLower (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
  module T = C.T
  module D = LowerCubeDirect.Direct Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = LowerCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt

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

    Z : Type
    Z = C.Z u∞ v∞ w∞ hL∞ hR∞ d

    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = C.u₆ u∞ v∞ w∞ hL∞ hR∞ d

    v₆ : finCellMap 6 W.Bs W.Bt
    v₆ = C.v₆ u∞ v∞ w∞ hL∞ hR∞ d

    w₆ : finCellMap 6 W.Cs W.Ct
    w₆ = C.w₆ u∞ v∞ w∞ hL∞ hR∞ d

    L : Type
    L = Path Z north north

    K : fst W.Yt 2 → fst W.Yt 3
    K = CW↪ W.Yt 2

    f : fst W.Yt 3 → Z
    f = T.prismCollapse 1

    module _ (x : fst W.Xs 1) where

      l : Path (fst W.Yt 2)
        (inl (fmap v₆ (2 , tt) (inl (SequenceMap.map W.S.f 1 x))))
        (inl (inl (SequenceMap.map W.T.f 1 (fmap u₆ (1 , tt) x))))
      l = cong (W.leftYt 1) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)

      q : Path (fst W.Yt 2)
        (inl (inl (SequenceMap.map W.T.f 1 (fmap u₆ (1 , tt) x))))
        (inr (inl (SequenceMap.map W.T.g 1 (fmap u₆ (1 , tt) x))))
      q = push (fmap u₆ (1 , tt) x)

      r : Path (fst W.Yt 2)
        (inr (inl (SequenceMap.map W.T.g 1 (fmap u₆ (1 , tt) x))))
        (inr (fmap w₆ (2 , tt) (inl (SequenceMap.map W.S.g 1 x))))
      r = sym (cong (W.rightYt 1)
        (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x))

      low : L
      low = cong (f ∘ K) (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (1 , tt) x)

      mid : L
      mid = cong f (G.three (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))
        (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
        (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x))

      m : L
      m = T.normalizedMeridian 1 (inr (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x)))

      ds : Path L m low
      ds j k = f (K (doubleCompPath-filler l q r j k))

      dt : Path L m mid
      dt j k = f (doubleCompPath-filler (cong K l) (cong K q) (cong K r) j k)

      de : Path L m (refl ∙∙ m ∙∙ refl)
      de = doubleCompPath-filler refl m refl

      cp : Path L low mid
      cp = cong (cong f) (cong-∙∙ K l q r)

      cd : Path L mid (refl ∙∙ m ∙∙ refl)
      cd = cong-∙∙ f (cong K l) (cong K q) (cong K r)

      g0 : Path L mid m
      g0 = G.normalize (CW↪ W.Xt 1 (fmap u₆ (1 , tt) x))
        (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
        (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x)

      v : Path L refl low
      v j k = T.prismNull 1 (C.F₂ u∞ v∞ w∞ hL∞ hR∞ d (push x k)) j

      n : Path L refl m
      n = T.prismCollapse-seam 1 (fmap u₆ (1 , tt) x)

      Q1 : Square {A = L} ds dt refl cp
      Q1 t j k = f (cong-∙∙-filler K l q r j t k)

      Q2 : Square {A = L} dt de refl cd
      Q2 t j k = cong-∙∙-filler f (cong K l) (cong K q) (cong K r) j t k

      V : Square {A = L} v n refl (sym ds)
      V t j k = T.prismNull 1 (doubleCompPath-filler l q r (~ t) k) j

      abstract
        lower-normalization-face : Path (Path L low m) (cp ∙ g0) (sym ds)
        lower-normalization-face =
          cong (cp ∙_) (cancel-square Q2) ∙ cancel-square Q1

        lower-null-pasting : Path (Path L refl m) (v ∙ (cp ∙ g0)) n
        lower-null-pasting =
          cong (v ∙_) lower-normalization-face
          ∙ sym (Square→compPath V)
          ∙ sym (lUnit n)
