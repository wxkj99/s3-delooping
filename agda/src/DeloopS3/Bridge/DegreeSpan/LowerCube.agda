{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerCube where

-- Lower-dimensional wrapper of the prism calculation.
-- Geometric stages 1/2/3; all approximation windows remain length 6.

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; cong-∙ ; cong-∙∙)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (fst ; _,_)
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; merid ; suspFun)
open import Cubical.CW.Base using (CWskel ; realise ; cofibCW ; CW↪)
open import Cubical.CW.Map using
  (cellMap ; realiseCellMap ; finCellMap ; module prefunctoriality)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import DeloopS3.Bridge.CellularPushout.Cellular using
  (restrictCell ; cellular-coefficients)
import DeloopS3.Bridge.DegreeSpan.TopCubeNull as Null
import DeloopS3.Bridge.DegreeSpan.TotalWindow as TotalWindow
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient
  using (module Quotient)

open FinSequenceMap

module LowerCube (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module W = TotalWindow.Window ℓ-zero Os Ls Rs Ot Lt Rt fs gs ft gt
  module S = Quotient Os Ls Rs fs gs
  module T = Quotient Ot Lt Rt ft gt
  module SourceNull = Null.TopCubeNull Os Ls Rs fs gs
  module TargetNull = Null.TopCubeNull Ot Lt Rt ft gt

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

    Φ₆ : finCellMap 6 W.Ys W.Yt
    Φ₆ = W.total-window u∞ v∞ w∞ hL∞ hR∞ d

    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = W.u u∞ v∞ w∞ hL∞ hR∞ d

    v₆ : finCellMap 6 W.Bs W.Bt
    v₆ = W.v u∞ v∞ w∞ hL∞ hR∞ d

    w₆ : finCellMap 6 W.Cs W.Ct
    w₆ = W.w u∞ v∞ w∞ hL∞ hR∞ d

    Q₂Φ : cofibCW 2 W.Ys → cofibCW 2 W.Yt
    Q₂Φ = prefunctoriality.fn+1/fn 6 Φ₆ (2 , tt)

    Q₁u : cofibCW 1 W.Xs → cofibCW 1 W.Xt
    Q₁u = prefunctoriality.fn+1/fn 6 u₆ (1 , tt)

    Z : Type
    Z = Susp (cofibCW 1 W.Xt)

    s : Susp (cofibCW 1 W.Xs) → Z
    s = suspFun Q₁u

    F₂ : fst W.Ys 2 → fst W.Yt 2
    F₂ = fmap Φ₆ (2 , tt)

    F₃ : fst W.Ys 3 → fst W.Yt 3
    F₃ = fmap Φ₆ (3 , tt)

    c₂ : (y : fst W.Ys 2)
      → Path (fst W.Yt 3)
          (CW↪ W.Yt 2 (F₂ y)) (F₃ (CW↪ W.Ys 2 y))
    c₂ = fcomm Φ₆ (2 , tt)

    abstract
      normalizedMeridian-natural : (z : cofibCW 1 W.Xs)
        → Path (Path Z north north)
            (cong s (S.normalizedMeridian 1 z))
            (T.normalizedMeridian 1 (Q₁u z))
      normalizedMeridian-natural z =
        cong-∙ s (merid z) (sym (merid (inl tt)))

      collapse-three-piece : (x : fst W.Xs 2)
        → Path (Path Z north north)
            (cong (T.prismCollapse 1)
              (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
            (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) x)))
      collapse-three-piece x =
        cong-∙∙ (T.prismCollapse 1)
          (cong (W.leftYt 2) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
          (push (fmap u₆ (2 , tt) x))
          (sym (cong (W.rightYt 2) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)))
        ∙ sym (doubleCompPath-filler refl
            (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) x))) refl)

      normalizedMeridian-natural-unfold : (z : cofibCW 1 W.Xs)
        → Path
            (Path (Path Z north north)
              (cong s (S.normalizedMeridian 1 z))
              (T.normalizedMeridian 1 (Q₁u z)))
            (normalizedMeridian-natural z)
            (cong-∙ s (merid z) (sym (merid (inl tt))))
      normalizedMeridian-natural-unfold z = refl

      collapse-three-piece-unfold : (x : fst W.Xs 2)
        → Path
            (Path (Path Z north north)
              (cong (T.prismCollapse 1)
                (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
              (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) x))))
            (collapse-three-piece x)
            (cong-∙∙ (T.prismCollapse 1)
              (cong (W.leftYt 2) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
              (push (fmap u₆ (2 , tt) x))
              (sym (cong (W.rightYt 2) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)))
            ∙ sym (doubleCompPath-filler refl
                (T.normalizedMeridian 1 (inr (fmap u₆ (2 , tt) x))) refl))
      collapse-three-piece-unfold x = refl

    H₀ : (z : fst W.Ys 3)
      → Path Z (T.prismCollapse 1 (F₃ z)) (s (S.prismCollapse 1 z))
    H₀ (inl b) = refl
    H₀ (inr c) = refl
    H₀ (push x i) j =
      (collapse-three-piece x ∙ sym (normalizedMeridian-natural (inr x))) j i

    expandedTop : (y : fst W.Ys 2)
      → Path Z north (T.prismCollapse 1 (F₃ (CW↪ W.Ys 2 y)))
    expandedTop y = T.prismNull 1 (F₂ y) ∙ cong (T.prismCollapse 1) (c₂ y)

    bottom : (y : fst W.Ys 2)
      → Path Z north (s (S.prismCollapse 1 (CW↪ W.Ys 2 y)))
    bottom y = cong s (S.prismNull 1 y)

    CubeAt : fst W.Ys 2 → Type
    CubeAt y = Square {A = Z}
      (expandedTop y) (bottom y) refl (H₀ (CW↪ W.Ys 2 y))

    Cube : Type
    Cube = (y : fst W.Ys 2) → CubeAt y

    abstract
      collapsed-comm-left : (b : fst W.Bs 2)
        → Path (Path Z north north)
            (cong (T.prismCollapse 1) (c₂ (inl b))) refl
      collapsed-comm-left b = refl

      collapsed-comm-right : (c : fst W.Cs 2)
        → Path (Path Z north north)
            (cong (T.prismCollapse 1) (c₂ (inr c))) refl
      collapsed-comm-right c = refl

      expandedTop-left : (b : fst W.Bs 2)
        → Path (Path Z north north)
            (expandedTop (inl b)) (refl {x = north} ∙ refl)
      expandedTop-left b = refl

      expandedTop-right : (c : fst W.Cs 2)
        → Path (Path Z north north)
            (expandedTop (inr c)) (refl {x = north} ∙ refl)
      expandedTop-right c = refl

    vertexL : (b : fst W.Bs 2) → CubeAt (inl b)
    vertexL b = sym (rUnit (refl {x = north}))

    vertexR : (c : fst W.Cs 2) → CubeAt (inr c)
    vertexR c = sym (rUnit (refl {x = north}))

    RemainingSeamCube : Type
    RemainingSeamCube = (x : fst W.Xs 1)
      → PathP (λ k → CubeAt (push x k))
          (vertexL (inl (SequenceMap.map W.S.f 1 x)))
          (vertexR (inl (SequenceMap.map W.S.g 1 x)))

    abstract
      cube-from-seam : RemainingSeamCube → Cube
      cube-from-seam K (inl b) = vertexL b
      cube-from-seam K (inr c) = vertexR c
      cube-from-seam K (push x k) = K x k

      quotient-push-expanded : (y : fst W.Ys 2)
        → Path
            (Path Z north (T.prismCollapse 1 (F₃ (CW↪ W.Ys 2 y))))
            (cong (T.prismRet 1 ∘ Q₂Φ) (push y))
            (expandedTop y)
      quotient-push-expanded y =
        cong-∙ (T.prismRet 1) (push (F₂ y)) (cong inr (c₂ y))

      overlap-meridian-push-expanded : (x : fst W.Xs 1)
        → Path
            (Path (Path Z north north)
              (T.normalizedMeridian 1 (inl tt))
              (T.normalizedMeridian 1
                (inr (fmap u₆ (2 , tt) (CW↪ W.Xs 1 x)))))
            (cong (T.normalizedMeridian 1 ∘ Q₁u) (push x))
            (cong (T.normalizedMeridian 1) (push (fmap u₆ (1 , tt) x))
              ∙ cong (T.normalizedMeridian 1 ∘ inr) (fcomm u₆ (1 , tt) x))
      overlap-meridian-push-expanded x =
        cong-∙ (T.normalizedMeridian 1)
          (push (fmap u₆ (1 , tt) x)) (cong inr (fcomm u₆ (1 , tt) x))

      cube-unexpand : Cube → (y : fst W.Ys 2)
        → Square {A = Z}
            (cong (T.prismRet 1 ∘ Q₂Φ) (push y))
            (bottom y) refl (H₀ (CW↪ W.Ys 2 y))
      cube-unexpand cube y = subst
        (λ p → Square {A = Z} p (bottom y) refl (H₀ (CW↪ W.Ys 2 y)))
        (sym (quotient-push-expanded y)) (cube y)

      prismRet-natural-from-seam : RemainingSeamCube
        → Path (cofibCW 2 W.Ys → Z)
            (T.prismRet 1 ∘ Q₂Φ) (s ∘ S.prismRet 1)
      prismRet-natural-from-seam K = funExt λ
        { (inl tt) → refl
        ; (inr z) → H₀ z
        ; (push y i) j → cube-unexpand (cube-from-seam K) y j i }

