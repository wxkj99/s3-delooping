{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCube where

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
import DeloopS3.Bridge.DegreeSpan.TopCubeDegree as FiniteDegree
import DeloopS3.Bridge.DegreeSpan.TopCubeNull as Null
import DeloopS3.Bridge.DegreeSpan.TotalWindow as TotalWindow
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient
  using (module Quotient)

open FinSequenceMap

-- Use the TotalWindow construction, including its actual fcomm.
-- Finite retraction naturality is reduced to the specified seam cube.
module TopCube (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
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

    Q₃Φ : cofibCW 3 W.Ys → cofibCW 3 W.Yt
    Q₃Φ = prefunctoriality.fn+1/fn 6 Φ₆ (3 , tt)

    Q₂u : cofibCW 2 W.Xs → cofibCW 2 W.Xt
    Q₂u = prefunctoriality.fn+1/fn 6 u₆ (2 , tt)

    Z : Type
    Z = Susp (cofibCW 2 W.Xt)

    s : Susp (cofibCW 2 W.Xs) → Z
    s = suspFun Q₂u

    F₃ : fst W.Ys 3 → fst W.Yt 3
    F₃ = fmap Φ₆ (3 , tt)

    F₄ : fst W.Ys 4 → fst W.Yt 4
    F₄ = fmap Φ₆ (4 , tt)

    c₃ : (y : fst W.Ys 3)
      → Path (fst W.Yt 4)
          (CW↪ W.Yt 3 (F₃ y)) (F₄ (CW↪ W.Ys 3 y))
    c₃ = fcomm Φ₆ (3 , tt)

    abstract
      normalizedMeridian-natural : (z : cofibCW 2 W.Xs)
        → Path (Path Z north north)
            (cong s (S.normalizedMeridian 2 z))
            (T.normalizedMeridian 2 (Q₂u z))
      normalizedMeridian-natural z =
        cong-∙ s (merid z) (sym (merid (inl tt)))

      collapse-three-piece : (x : fst W.Xs 3)
        → Path (Path Z north north)
            (cong (T.prismCollapse 2)
              (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x))
            (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) x)))
      collapse-three-piece x =
        cong-∙∙ (T.prismCollapse 2)
          (cong (W.leftYt 3) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x))
          (push (fmap u₆ (3 , tt) x))
          (sym (cong (W.rightYt 3) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)))
        ∙ sym (doubleCompPath-filler refl
            (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) x))) refl)

      normalizedMeridian-natural-unfold : (z : cofibCW 2 W.Xs)
        → Path
            (Path (Path Z north north)
              (cong s (S.normalizedMeridian 2 z))
              (T.normalizedMeridian 2 (Q₂u z)))
            (normalizedMeridian-natural z)
            (cong-∙ s (merid z) (sym (merid (inl tt))))
      normalizedMeridian-natural-unfold z = refl

      collapse-three-piece-unfold : (x : fst W.Xs 3)
        → Path
            (Path (Path Z north north)
              (cong (T.prismCollapse 2)
                (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x))
              (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) x))))
            (collapse-three-piece x)
            (cong-∙∙ (T.prismCollapse 2)
              (cong (W.leftYt 3) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x))
              (push (fmap u₆ (3 , tt) x))
              (sym (cong (W.rightYt 3) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)))
            ∙ sym (doubleCompPath-filler refl
                (T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) x))) refl))
      collapse-three-piece-unfold x = refl

    -- This finite homotopy is specified independently of TopRetractionNatural.H.
    -- Keep these clauses transparent for the cube's vertex boundaries.
    H₀ : (z : fst W.Ys 4)
      → Path Z (T.prismCollapse 2 (F₄ z)) (s (S.prismCollapse 2 z))
    H₀ (inl b) = refl
    H₀ (inr c) = refl
    H₀ (push x i) j =
      (collapse-three-piece x ∙ sym (normalizedMeridian-natural (inr x))) j i

    expandedTop : (y : fst W.Ys 3)
      → Path Z north (T.prismCollapse 2 (F₄ (CW↪ W.Ys 3 y)))
    expandedTop y = T.prismNull 2 (F₃ y) ∙ cong (T.prismCollapse 2) (c₃ y)

    bottom : (y : fst W.Ys 3)
      → Path Z north (s (S.prismCollapse 2 (CW↪ W.Ys 3 y)))
    bottom y = cong s (S.prismNull 2 y)

    CubeAt : fst W.Ys 3 → Type
    CubeAt y = Square {A = Z}
      (expandedTop y) (bottom y) refl (H₀ (CW↪ W.Ys 3 y))

    Cube : Type
    Cube = (y : fst W.Ys 3) → CubeAt y

    abstract
      collapsed-comm-left : (b : fst W.Bs 3)
        → Path (Path Z north north)
            (cong (T.prismCollapse 2) (c₃ (inl b))) refl
      collapsed-comm-left b = refl

      collapsed-comm-right : (c : fst W.Cs 3)
        → Path (Path Z north north)
            (cong (T.prismCollapse 2) (c₃ (inr c))) refl
      collapsed-comm-right c = refl

      expandedTop-left : (b : fst W.Bs 3)
        → Path (Path Z north north)
            (expandedTop (inl b)) (refl {x = north} ∙ refl)
      expandedTop-left b = refl

      expandedTop-right : (c : fst W.Cs 3)
        → Path (Path Z north north)
            (expandedTop (inr c)) (refl {x = north} ∙ refl)
      expandedTop-right c = refl

    -- Transparent witnesses: their exact squares fix two seam-cube faces.
    vertexL : (b : fst W.Bs 3) → CubeAt (inl b)
    vertexL b = sym (rUnit (refl {x = north}))

    vertexR : (c : fst W.Cs 3) → CubeAt (inr c)
    vertexR c = sym (rUnit (refl {x = north}))

    -- The seam cube is this PathP, with all six faces fixed.
    -- For seam coordinate k, naturality coordinate t, path coordinate j:
    -- t=0: expandedTop (push x k) j
    -- t=1: bottom (push x k) j
    -- j=0: north
    -- j=1: H₀ (CW↪ W.Ys 3 (push x k)) t
    -- k=0: vertexL (inl (SequenceMap.map W.S.f 2 x)) t j
    -- k=1: vertexR (inl (SequenceMap.map W.S.g 2 x)) t j
    -- The inner inl below is the strict skeleton inclusion.
    RemainingSeamCube : Type
    RemainingSeamCube = (x : fst W.Xs 2)
      → PathP (λ k → CubeAt (push x k))
          (vertexL (inl (SequenceMap.map W.S.f 2 x)))
          (vertexR (inl (SequenceMap.map W.S.g 2 x)))

    abstract
      cube-from-seam : RemainingSeamCube → Cube
      cube-from-seam K (inl b) = vertexL b
      cube-from-seam K (inr c) = vertexR c
      cube-from-seam K (push x k) = K x k

      quotient-push-expanded : (y : fst W.Ys 3)
        → Path
            (Path Z north (T.prismCollapse 2 (F₄ (CW↪ W.Ys 3 y))))
            (cong (T.prismRet 2 ∘ Q₃Φ) (push y))
            (expandedTop y)
      quotient-push-expanded y =
        cong-∙ (T.prismRet 2) (push (F₃ y)) (cong inr (c₃ y))

      overlap-meridian-push-expanded : (x : fst W.Xs 2)
        → Path
            (Path (Path Z north north)
              (T.normalizedMeridian 2 (inl tt))
              (T.normalizedMeridian 2
                (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))))
            (cong (T.normalizedMeridian 2 ∘ Q₂u) (push x))
            (cong (T.normalizedMeridian 2) (push (fmap u₆ (2 , tt) x))
              ∙ cong (T.normalizedMeridian 2 ∘ inr) (fcomm u₆ (2 , tt) x))
      overlap-meridian-push-expanded x =
        cong-∙ (T.normalizedMeridian 2)
          (push (fmap u₆ (2 , tt) x)) (cong inr (fcomm u₆ (2 , tt) x))

      cube-unexpand : Cube → (y : fst W.Ys 3)
        → Square {A = Z}
            (cong (T.prismRet 2 ∘ Q₃Φ) (push y))
            (bottom y) refl (H₀ (CW↪ W.Ys 3 y))
      cube-unexpand cube y = subst
        (λ p → Square {A = Z} p (bottom y) refl (H₀ (CW↪ W.Ys 3 y)))
        (sym (quotient-push-expanded y)) (cube y)

      prismRet-natural-from-seam : RemainingSeamCube
        → Path (cofibCW 3 W.Ys → Z)
            (T.prismRet 2 ∘ Q₃Φ) (s ∘ S.prismRet 2)
      prismRet-natural-from-seam K = funExt λ
        { (inl tt) → refl
        ; (inr z) → H₀ z
        ; (push y i) j → cube-unexpand (cube-from-seam K) y j i }

    -- Changing the boundary requires agreement with H₀; the independently
    -- specified TopRetractionNatural.H is not identified with H₀ here.
    CubeFor :
      (h : (z : fst W.Ys 4)
        → Path Z (T.prismCollapse 2 (F₄ z)) (s (S.prismCollapse 2 z)))
      → Type
    CubeFor h = (y : fst W.Ys 3)
      → Square {A = Z}
          (expandedTop y) (bottom y) refl (h (CW↪ W.Ys 3 y))

    BoundaryAgreement :
      (h : (z : fst W.Ys 4)
        → Path Z (T.prismCollapse 2 (F₄ z)) (s (S.prismCollapse 2 z)))
      → Type
    BoundaryAgreement h = (z : fst W.Ys 4)
      → Path (Path Z (T.prismCollapse 2 (F₄ z)) (s (S.prismCollapse 2 z)))
          (H₀ z) (h z)

    abstract
      cube-for-boundary-from-seam : RemainingSeamCube
        → (h : (z : fst W.Ys 4)
            → Path Z (T.prismCollapse 2 (F₄ z)) (s (S.prismCollapse 2 z)))
        → BoundaryAgreement h → CubeFor h
      cube-for-boundary-from-seam K h e y = subst
        (λ r → Square {A = Z} (expandedTop y) (bottom y) refl r)
        (e (CW↪ W.Ys 3 y)) (cube-from-seam K y)

    -- A finite window is not itself a cellMap at all stages. If full maps
    -- with these exact restrictions are supplied, the degree conclusion
    -- needs the seam cube but does not need agreement with the protected H.
    module Global (u : cellMap W.Xs W.Xt) (Φ : cellMap W.Ys W.Yt) where
      private
        module D = FiniteDegree.FiniteRetractionDegree
          W.Xs W.Xt W.Ys W.Yt u Φ (S.prismRet 2) (T.prismRet 2)

      abstract
        top-R-natural-from-seam
          : restrictCell u 6 ≡ u₆
          → restrictCell Φ 6 ≡ Φ₆
          → RemainingSeamCube
          → compGroupHom (cellular-coefficients Φ 3) (T.R 2)
           ≡ compGroupHom (S.R 2) (cellular-coefficients u 2)
        top-R-natural-from-seam ue fe K =
          D.finite-degree-natural u₆ Φ₆ ue fe (prismRet-natural-from-seam K)
