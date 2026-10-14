{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeClose where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.HITs.Pushout.Base using (Pushout ; inl ; inr ; push)

-- Naturality of normalization for the bare three-piece construction.
-- TopCubeAssemble compares it with the specified total-map seam cube.
module CollapsedThreePiece {ℓ : Level} (X L R Z : Type ℓ)
  (f : X → L) (g : X → R) (z : Z) (m : X → z ≡ z) where

  Y : Type ℓ
  Y = Pushout f g

  collapse : Y → Z
  collapse (inl _) = z
  collapse (inr _) = z
  collapse (push x k) = m x k

  three : (x : X) {a : L} {b : R}
    → (l : a ≡ f x) (r : b ≡ g x) → Path Y (inl a) (inr b)
  three x l r = cong inl l ∙∙ push x ∙∙ sym (cong inr r)

  -- Transparent: its endpoint instances are faces of normalize-square.
  normalize : (x : X) {a : L} {b : R}
    → (l : a ≡ f x) (r : b ≡ g x)
    → Path (z ≡ z) (cong collapse (three x l r)) (m x)
  normalize x l r =
    cong-∙∙ collapse (cong inl l) (push x) (sym (cong inr r))
    ∙ sym (doubleCompPath-filler (refl {x = z}) (m x) (refl {x = z}))

  module _ {a0 a1 : L} {b0 b1 : R} {x0 x1 : X}
    (a : a0 ≡ a1) (b : b0 ≡ b1) (u : x0 ≡ x1)
    (l0 : a0 ≡ f x0) (l1 : a1 ≡ f x1)
    (r0 : b0 ≡ g x0) (r1 : b1 ≡ g x1)
    (HL : Square l0 l1 a (cong f u))
    (HR : Square r0 r1 b (cong g u)) where

    three-square : Square {A = Y}
      (three x0 l0 r0) (three x1 l1 r1) (cong inl a) (cong inr b)
    three-square j = three (u j) (HL j) (HR j)

    abstract
      -- t is normalization, j varies the input data, k is the loop coordinate.
      -- Both input homotopies are retained with their varying endpoints.
      normalize-square : Square {A = z ≡ z}
        (λ j k → collapse (three-square j k)) (cong m u)
        (normalize x0 l0 r0) (normalize x1 l1 r1)
      normalize-square t j = normalize (u j) (HL j) (HR j) t

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
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube

open FinSequenceMap

-- A concrete bare cube, not an unfolding of the abstract S_total.
module ActualWindow (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
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
      (fst W.Xt 3) (fst W.Bt 4) (fst W.Ct 4) Z
      (λ x → inl (SequenceMap.map W.T.f 3 x))
      (λ x → inl (SequenceMap.map W.T.g 3 x))
      north (λ x → T.normalizedMeridian 2 (inr x))

    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = W.u u∞ v∞ w∞ hL∞ hR∞ d

    v₆ : finCellMap 6 W.Bs W.Bt
    v₆ = W.v u∞ v∞ w∞ hL∞ hR∞ d

    w₆ : finCellMap 6 W.Cs W.Ct
    w₆ = W.w u∞ v∞ w∞ hL∞ hR∞ d

    uStep : (x : fst W.Xs 2)
      → Path (fst W.Xt 3)
          (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))
          (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))
    uStep x = fcomm u₆ (2 , tt) x

    aStep : (x : fst W.Xs 2)
      → Path (fst W.Bt 4)
          (CW↪ W.Bt 3 (fmap v₆ (3 , tt) (inl (SequenceMap.map W.S.f 2 x))))
          (fmap v₆ (4 , tt) (CW↪ W.Bs 3 (inl (SequenceMap.map W.S.f 2 x))))
    aStep x = fcomm v₆ (3 , tt) (inl (SequenceMap.map W.S.f 2 x))

    bStep : (x : fst W.Xs 2)
      → Path (fst W.Ct 4)
          (CW↪ W.Ct 3 (fmap w₆ (3 , tt) (inl (SequenceMap.map W.S.g 2 x))))
          (fmap w₆ (4 , tt) (CW↪ W.Cs 3 (inl (SequenceMap.map W.S.g 2 x))))
    bStep x = fcomm w₆ (3 , tt) (inl (SequenceMap.map W.S.g 2 x))

    l0 : (x : fst W.Xs 2)
      → Path (fst W.Bt 4)
          (CW↪ W.Bt 3 (fmap v₆ (3 , tt) (inl (SequenceMap.map W.S.f 2 x))))
          (inl (SequenceMap.map W.T.f 3 (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))))
    l0 x = cong (CW↪ W.Bt 3) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)

    l1 : (x : fst W.Xs 2)
      → Path (fst W.Bt 4)
          (fmap v₆ (4 , tt) (CW↪ W.Bs 3 (inl (SequenceMap.map W.S.f 2 x))))
          (inl (SequenceMap.map W.T.f 3 (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))))
    l1 x = W.hatL u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x)

    r0 : (x : fst W.Xs 2)
      → Path (fst W.Ct 4)
          (CW↪ W.Ct 3 (fmap w₆ (3 , tt) (inl (SequenceMap.map W.S.g 2 x))))
          (inl (SequenceMap.map W.T.g 3 (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))))
    r0 x = cong (CW↪ W.Ct 3) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)

    r1 : (x : fst W.Xs 2)
      → Path (fst W.Ct 4)
          (fmap w₆ (4 , tt) (CW↪ W.Cs 3 (inl (SequenceMap.map W.S.g 2 x))))
          (inl (SequenceMap.map W.T.g 3 (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))))
    r1 x = W.hatR u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x)

    HL : (x : fst W.Xs 2)
      → Square {A = fst W.Bt 4} (l0 x) (l1 x) (aStep x)
          (cong (λ z → inl (SequenceMap.map W.T.f 3 z)) (uStep x))
    HL x = W.hatL-coh u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x

    HR : (x : fst W.Xs 2)
      → Square {A = fst W.Ct 4} (r0 x) (r1 x) (bStep x)
          (cong (λ z → inl (SequenceMap.map W.T.g 3 z)) (uStep x))
    HR x = W.hatR-coh u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x

    bare-comm : (x : fst W.Xs 2)
      → Square {A = fst W.Yt 4}
          (G.three (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x)) (l0 x) (r0 x))
          (G.three (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)) (l1 x) (r1 x))
          (cong inl (aStep x)) (cong inr (bStep x))
    bare-comm x = G.three-square (aStep x) (bStep x) (uStep x)
      (l0 x) (l1 x) (r0 x) (r1 x) (HL x) (HR x)

    abstract
      bare-comm-normalizes : (x : fst W.Xs 2)
        → Square {A = Path Z north north}
            (λ j k → T.prismCollapse 2 (bare-comm x j k))
            (cong (λ z → T.normalizedMeridian 2 (inr z)) (uStep x))
            (G.normalize (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x)) (l0 x) (r0 x))
            (G.normalize (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)) (l1 x) (r1 x))
      bare-comm-normalizes x = G.normalize-square (aStep x) (bStep x) (uStep x)
        (l0 x) (l1 x) (r0 x) (r1 x) (HL x) (HR x)

    -- Comparison of the collapsed total-map commutation with bare normalization.
    CollapsedCommAgreement : Type
    CollapsedCommAgreement = (x : fst W.Xs 2) →
      let
        low : Path Z north north
        low = cong (T.prismCollapse 2 ∘ CW↪ W.Yt 3)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)
        high : Path Z north north
        high = cong (T.prismCollapse 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x))
        actual : Path (Path Z north north) low high
        actual = λ j k → T.prismCollapse 2
          (C.c₃ u∞ v∞ w∞ hL∞ hR∞ d (push x k) j)
        raw : Path (Path Z north north) low high
        raw = cong (cong (T.prismCollapse 2))
          (cong-∙∙ (CW↪ W.Yt 3)
            (cong (W.leftYt 2) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
            (push (fmap u₆ (2 , tt) x))
            (sym (cong (W.rightYt 2) (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))))
          ∙ (λ j k → T.prismCollapse 2 (bare-comm x j k))
      in Path (Path (Path Z north north) low high) actual raw

    -- Comparison with the abstract collapse-three-piece normalization.
    UpperNormalizationAgreement : Type
    UpperNormalizationAgreement = (x : fst W.Xs 3) →
      let
        low : Path Z north north
        low = cong (T.prismCollapse 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)
        high : Path Z north north
        high = T.normalizedMeridian 2 (inr (fmap u₆ (3 , tt) x))
        actual : Path (Path Z north north) low high
        actual = C.collapse-three-piece u∞ v∞ w∞ hL∞ hR∞ d x
        normalized : Path (Path Z north north) low high
        normalized = G.normalize (fmap u₆ (3 , tt) x)
          (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)
          (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) x)
      in Path (Path (Path Z north north) low high) actual normalized

    -- The seam condition retains the exact PathP boundary, including source-null
    -- and cancellation coherence; TopCubeAssemble constructs it.
    RemainingSeamCube : Type
    RemainingSeamCube = (x : fst W.Xs 2)
      → PathP (λ k → C.CubeAt u∞ v∞ w∞ hL∞ hR∞ d (push x k))
          (C.vertexL u∞ v∞ w∞ hL∞ hR∞ d (inl (SequenceMap.map W.S.f 2 x)))
          (C.vertexR u∞ v∞ w∞ hL∞ hR∞ d (inl (SequenceMap.map W.S.g 2 x)))

    prismRet-natural-from-residual : RemainingSeamCube
      → Path (cofibCW 3 W.Ys → Z)
          (T.prismRet 2 ∘ C.Q₃Φ u∞ v∞ w∞ hL∞ hR∞ d)
          (C.s u∞ v∞ w∞ hL∞ hR∞ d ∘ S.prismRet 2)
    prismRet-natural-from-residual = C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d

    -- Only a unit-adjusted H₀; no identification with the protected H.
    -- That protected construction also requires global Φ, u and
    -- SeamCompatibility; the finite datum d alone does not instantiate it.
    hUnit : (z : fst W.Ys 4)
      → Path Z
          (T.prismCollapse 2 (C.F₄ u∞ v∞ w∞ hL∞ hR∞ d z))
          (C.s u∞ v∞ w∞ hL∞ hR∞ d (S.prismCollapse 2 z))
    hUnit z = funExt⁻ (refl ∙ funExt (C.H₀ u∞ v∞ w∞ hL∞ hR∞ d)) z

    hUnit-boundary-agreement : C.BoundaryAgreement u∞ v∞ w∞ hL∞ hR∞ d hUnit
    hUnit-boundary-agreement z = cong (λ p → funExt⁻ p z)
      (lUnit (funExt (C.H₀ u∞ v∞ w∞ hL∞ hR∞ d)))
