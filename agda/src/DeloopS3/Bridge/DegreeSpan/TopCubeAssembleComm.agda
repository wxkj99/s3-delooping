{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeAssembleComm where

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
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopCubeClose as TopCubeClose
import DeloopS3.Bridge.DegreeSpan.TopCubeDirect as TopCubeDirect

open FinSequenceMap

abstract
  mapped-left-whisker : ∀ {ℓ ℓ'}
    (A : I → Type ℓ) (B : Type ℓ') (F : (i : I) → A i → B)
    {a0 a0' : A i0} {a1 : A i1}
    (p : Path (A i0) a0 a0') (q : PathP A a0' a1)
    → Path (Path B (F i0 a0) (F i1 a1))
        (λ i → F i ((p ◁ q) i))
        (cong (F i0) p ∙ (λ i → F i (q i)))
  mapped-left-whisker A B F {a0} {a0'} {a1} p q =
    comparison ∙ sym (leftright cp cq)
    where
    cp : Path B (F i0 a0) (F i0 a0')
    cp = cong (F i0) p

    cq : Path B (F i0 a0') (F i1 a1)
    cq i = F i (q i)

    mapped : Path B (F i0 a0) (F i1 a1)
    mapped i = F i ((p ◁ q) i)

    comparison : Path (Path B (F i0 a0) (F i1 a1))
      mapped (cp ∙∙ cq ∙∙ refl {x = F i1 a1})
    comparison t i = hcomp
      (λ k → λ
        { (t = i0) → F i
            (doubleWhiskFiller {A = A} p q
              (refl {x = a1}) k i)
        ; (t = i1) → doubleCompPath-filler cp cq
            (refl {x = F i1 a1}) k i
        ; (i = i0) → F i0 (p (~ k))
        ; (i = i1) → F i1 a1
        })
      (F i (q i))

module AssembleComm (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module A = TopCubeClose.ActualWindow Os Ls Rs Ot Lt Rt fs gs ft gt
  module D = TopCubeDirect.Direct Os Ls Rs Ot Lt Rt fs gs ft gt
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
      module _ (x : fst W.Xs 2) where
        low : Path Z north north
        low = cong (T.prismCollapse 2 ∘ CW↪ W.Yt 3)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)

        bareLow : Path Z north north
        bareLow = cong (T.prismCollapse 2)
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)

        upper : Path Z north north
        upper = cong (T.prismCollapse 2)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x))

        normalizedLow : Path Z north north
        normalizedLow = T.normalizedMeridian 2
          (inr (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x)))

        high : Path Z north north
        high = T.normalizedMeridian 2
          (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))

        boundary : I → Type
        boundary j = Path (fst W.Yt 4)
          (inl (A.aStep u∞ v∞ w∞ hL∞ hR∞ d x j))
          (inr (A.bStep u∞ v∞ w∞ hL∞ hR∞ d x j))

        p : Path (boundary i0)
          (cong (CW↪ W.Yt 3)
            (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)
        p = cong-∙∙ (CW↪ W.Yt 3)
          (cong (W.leftYt 2) (W.hatL u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
          (push (fmap u₆ (2 , tt) x))
          (sym (cong (W.rightYt 2)
            (W.hatR u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)))

        q : PathP boundary
          (A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0)
          (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x))
        q = A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x

        F : (j : I) → boundary j → Path Z north north
        F j pth = cong (T.prismCollapse 2) pth

        cp : Path (Path Z north north) low bareLow
        cp = cong (cong (T.prismCollapse 2)) p

        bare : Path (Path Z north north) bareLow upper
        bare j k = T.prismCollapse 2 (q j k)

        actual : Path (Path Z north north) low upper
        actual j k = T.prismCollapse 2
          (C.c₃ u∞ v∞ w∞ hL∞ hR∞ d (push x k) j)

        g0 : Path (Path Z north north) bareLow normalizedLow
        g0 = G.normalize (CW↪ W.Xt 2 (fmap u₆ (2 , tt) x))
          (A.l0 u∞ v∞ w∞ hL∞ hR∞ d x)
          (A.r0 u∞ v∞ w∞ hL∞ hR∞ d x)

        g1 : Path (Path Z north north) upper high
        g1 = G.normalize (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x))
          (A.l1 u∞ v∞ w∞ hL∞ hR∞ d x)
          (A.r1 u∞ v∞ w∞ hL∞ hR∞ d x)

        ustep : Path (Path Z north north) normalizedLow high
        ustep = D.targetStep u∞ v∞ w∞ hL∞ hR∞ d x

    abstract
      collapsed-comm-agreement : A.CollapsedCommAgreement u∞ v∞ w∞ hL∞ hR∞ d
      collapsed-comm-agreement x =
        cong (λ sq j k → T.prismCollapse 2 (sq j k))
          (W.S_total-unfold u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)
        ∙ mapped-left-whisker (boundary x) (Path Z north north) (F x)
            {a0 = cong (CW↪ W.Yt 3)
              (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x)}
            {a0' = A.bare-comm u∞ v∞ w∞ hL∞ hR∞ d x i0}
            {a1 = W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (3 , tt) (CW↪ W.Xs 2 x)}
            (p x) (q x)

      actual-overlap-pasting : (x : fst W.Xs 2)
        → Path
            (Path (Path Z north north)
              (cong (T.prismCollapse 2 ∘ CW↪ W.Yt 3)
                (W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d (2 , tt) x))
              (T.normalizedMeridian 2
                (inr (fmap u₆ (3 , tt) (CW↪ W.Xs 2 x)))))
            ((cp x ∙ g0 x) ∙ ustep x)
            (actual x ∙ g1 x)
      actual-overlap-pasting x =
        sym (assoc (cp x) (g0 x) (ustep x))
        ∙ cong (cp x ∙_) (D.bare-overlap-pasting u∞ v∞ w∞ hL∞ hR∞ d x)
        ∙ assoc (cp x) (bare x) (g1 x)
        ∙ cong (_∙ g1 x) (sym (collapsed-comm-agreement x))
