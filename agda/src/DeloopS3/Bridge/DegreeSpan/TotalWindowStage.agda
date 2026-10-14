{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TotalWindowStage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lUnit ; cong-∙ ; cong-∙∙)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Base using (Fin ; injectSuc ; fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.SequentialColimit using (incl ; fincl)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.CW.Base
open import Cubical.CW.Properties using (CW₀-empty)
open import Cubical.CW.Map using
  (cellMap ; realiseCellMap ; finCellMap ; composeFinCellMap ; finCellMap↓)
open import Cubical.CW.Homotopy using (finCellHom)
open import Cubical.CW.Approximation using (finCellApprox ; finCellHomRel)
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.DegreeSpan.TotalWindowSquare using (rebase-square)

open FinSequenceMap
open finCellHom

restrictCell : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
  → cellMap C D → (m : ℕ) → finCellMap m C D
fmap (restrictCell f m) n = SequenceMap.map f (fst n)
fcomm (restrictCell f m) n = SequenceMap.comm f (fst n)

module Window (ℓ : Level) (Os Ls Rs Ot Lt Rt : CWskel ℓ)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module S = CWPushout ℓ Os Ls Rs fs gs
  module T = CWPushout ℓ Ot Lt Rt ft gt

  Xs Bs Cs Xt Bt Ct Ys Yt : CWskel ℓ
  Xs = S.B
  Bs = S.C
  Cs = S.D
  Xt = T.B
  Bt = T.C
  Ct = T.D
  Ys = S.pushoutSkel
  Yt = T.pushoutSkel

  leftYt : (n : ℕ) → fst Bt (suc n) → fst Yt (suc n)
  leftYt n = inl

  rightYt : (n : ℕ) → fst Ct (suc n) → fst Yt (suc n)
  rightYt n = inr

  module _
    (u∞ : realise Xs → realise Xt)
    (v∞ : realise Bs → realise Bt)
    (w∞ : realise Cs → realise Ct)
    (hL∞ : (x : realise Xs)
      → v∞ (realiseCellMap {C = Xs} {D = Bs} S.f x)
      ≡ realiseCellMap {C = Xt} {D = Bt} T.f (u∞ x))
    (hR∞ : (x : realise Xs)
      → w∞ (realiseCellMap {C = Xs} {D = Cs} S.g x)
      ≡ realiseCellMap {C = Xt} {D = Ct} T.g (u∞ x)) where

    F_L : finCellApprox Bs Bt v∞ 6 → finCellMap 5 Xs Bt
    F_L aL = composeFinCellMap 5 (finCellMap↓ (fst aL)) (restrictCell S.f 5)

    G_L : finCellApprox Xs Xt u∞ 6 → finCellMap 5 Xs Bt
    G_L aO = composeFinCellMap 5 (restrictCell T.f 5) (finCellMap↓ (fst aO))

    F_R : finCellApprox Cs Ct w∞ 6 → finCellMap 5 Xs Ct
    F_R aR = composeFinCellMap 5 (finCellMap↓ (fst aR)) (restrictCell S.g 5)

    G_R : finCellApprox Xs Xt u∞ 6 → finCellMap 5 Xs Ct
    G_R aO = composeFinCellMap 5 (restrictCell T.g 5) (finCellMap↓ (fst aO))

    markingL : (aO : finCellApprox Xs Xt u∞ 6)
      (aL : finCellApprox Bs Bt v∞ 6) (n : Fin 6) (x : fst Xs (fst n))
      → Path (realise Bt) (incl (fmap (F_L aL) n x)) (incl (fmap (G_L aO) n x))
    markingL aO aL n x =
      funExt⁻ (snd aL) (fincl (injectSuc n) (SequenceMap.map S.f (fst n) x))
      ∙∙ hL∞ (incl x)
      ∙∙ sym (cong (realiseCellMap {C = Xt} {D = Bt} T.f)
           (funExt⁻ (snd aO) (fincl (injectSuc n) x)))

    markingR : (aO : finCellApprox Xs Xt u∞ 6)
      (aR : finCellApprox Cs Ct w∞ 6) (n : Fin 6) (x : fst Xs (fst n))
      → Path (realise Ct) (incl (fmap (F_R aR) n x)) (incl (fmap (G_R aO) n x))
    markingR aO aR n x =
      funExt⁻ (snd aR) (fincl (injectSuc n) (SequenceMap.map S.g (fst n) x))
      ∙∙ hR∞ (incl x)
      ∙∙ sym (cong (realiseCellMap {C = Xt} {D = Ct} T.g)
           (funExt⁻ (snd aO) (fincl (injectSuc n) x)))

    record FiniteSpan6 : Type ℓ where
      field
        aO : finCellApprox Xs Xt u∞ 6
        aL : finCellApprox Bs Bt v∞ 6
        aR : finCellApprox Cs Ct w∞ 6
        H_L : finCellHomRel 5 (F_L aL) (G_L aO) (markingL aO aL)
        H_R : finCellHomRel 5 (F_R aR) (G_R aO) (markingR aO aR)

    module _ (d : FiniteSpan6) where
      open FiniteSpan6 d

      u : finCellMap 6 Xs Xt
      u = fst aO
      v : finCellMap 6 Bs Bt
      v = fst aL
      w : finCellMap 6 Cs Ct
      w = fst aR
      HL : finCellHom 5 (F_L aL) (G_L aO)
      HL = fst H_L
      HR : finCellHom 5 (F_R aR) (G_R aO)
      HR = fst H_R

      hatL : (n : Fin 6) (x : fst Xs (fst n))
        → fmap v (fsuc n) (inl (SequenceMap.map S.f (fst n) x))
        ≡ inl (SequenceMap.map T.f (fst n) (fmap u (injectSuc n) x))
      hatL n x = sym (fcomm v n (SequenceMap.map S.f (fst n) x)) ∙ fhom HL n x

      hatR : (n : Fin 6) (x : fst Xs (fst n))
        → fmap w (fsuc n) (inl (SequenceMap.map S.g (fst n) x))
        ≡ inl (SequenceMap.map T.g (fst n) (fmap u (injectSuc n) x))
      hatR n x = sym (fcomm w n (SequenceMap.map S.g (fst n) x)) ∙ fhom HR n x

      stage-seam : (n : Fin 6) (x : fst Xs (fst n))
        → Path (fst Yt (suc (fst n)))
          (inl (fmap v (fsuc n) (inl (SequenceMap.map S.f (fst n) x))))
          (inr (fmap w (fsuc n) (inl (SequenceMap.map S.g (fst n) x))))
      stage-seam n x = cong (leftYt (fst n)) (hatL n x)
        ∙∙ push (fmap u (injectSuc n) x) ∙∙ sym (cong (rightYt (fst n)) (hatR n x))

      stage : (n : Fin 6) → fst Ys (suc (fst n)) → fst Yt (suc (fst n))
      stage n (inl y) = inl (fmap v (fsuc n) y)
      stage n (inr z) = inr (fmap w (fsuc n) z)
      stage n (push x i) = stage-seam n x i

      total-stage : (n : Fin 7) → fst Ys (fst n) → fst Yt (fst n)
      total-stage (zero , p) x = Empty.rec (CW₀-empty Ys x)
      total-stage (suc n , p) = stage (n , p)

      abstract
        -- Remove precisely the two units introduced by composite commutation.
        HL-normal : (n : Fin 5) (x : fst Xs (fst n))
          → Square
            (cong (CW↪ Bt (suc (fst n))) (fhom HL (injectSuc n) x))
            (fhom HL (fsuc n) (inl x))
            (cong (CW↪ Bt (suc (fst n))) (fcomm v (injectSuc n) (SequenceMap.map S.f (fst n) x)))
            (cong (CW↪ Bt (suc (fst n))) (cong (SequenceMap.map T.f (suc (fst n)))
              (fcomm u (injectSuc n) x)))
        HL-normal n x = subst2
          (λ l r → Square (cong (CW↪ Bt (suc (fst n))) (fhom HL (injectSuc n) x))
            (fhom HL (fsuc n) (inl x)) l r)
          (cong (cong (CW↪ Bt (suc (fst n)))) (sym (rUnit
            (fcomm v (injectSuc n) (SequenceMap.map S.f (fst n) x)))))
          (cong (cong (CW↪ Bt (suc (fst n)))) (sym (lUnit
            (cong (SequenceMap.map T.f (suc (fst n))) (fcomm u (injectSuc n) x)))))
          (fcoh HL n x)

        HR-normal : (n : Fin 5) (x : fst Xs (fst n))
          → Square
            (cong (CW↪ Ct (suc (fst n))) (fhom HR (injectSuc n) x))
            (fhom HR (fsuc n) (inl x))
            (cong (CW↪ Ct (suc (fst n))) (fcomm w (injectSuc n) (SequenceMap.map S.g (fst n) x)))
            (cong (CW↪ Ct (suc (fst n))) (cong (SequenceMap.map T.g (suc (fst n)))
              (fcomm u (injectSuc n) x)))
        HR-normal n x = subst2
          (λ l r → Square (cong (CW↪ Ct (suc (fst n))) (fhom HR (injectSuc n) x))
            (fhom HR (fsuc n) (inl x)) l r)
          (cong (cong (CW↪ Ct (suc (fst n)))) (sym (rUnit
            (fcomm w (injectSuc n) (SequenceMap.map S.g (fst n) x)))))
          (cong (cong (CW↪ Ct (suc (fst n)))) (sym (lUnit
            (cong (SequenceMap.map T.g (suc (fst n))) (fcomm u (injectSuc n) x)))))
          (fcoh HR n x)

        hatL-coh : (n : Fin 5) (x : fst Xs (fst n))
          → Square (cong (CW↪ Bt (suc (fst n))) (hatL (injectSuc n) x)) (hatL (fsuc n) (inl x))
            (fcomm v (fsuc n) (inl (SequenceMap.map S.f (fst n) x)))
            (cong (CW↪ Bt (suc (fst n))) (cong (SequenceMap.map T.f (suc (fst n)))
              (fcomm u (injectSuc n) x)))
        hatL-coh n x =
          cong-∙ (CW↪ Bt (suc (fst n)))
            (sym (fcomm v (injectSuc n) (SequenceMap.map S.f (fst n) x)))
            (fhom HL (injectSuc n) x)
          ◁ rebase-square
            (cong (CW↪ Bt (suc (fst n))) (fhom HL (injectSuc n) x))
            (fhom HL (fsuc n) (inl x))
            (cong (CW↪ Bt (suc (fst n))) (fcomm v (injectSuc n) (SequenceMap.map S.f (fst n) x)))
            (cong (CW↪ Bt (suc (fst n))) (cong (SequenceMap.map T.f (suc (fst n)))
              (fcomm u (injectSuc n) x)))
            (fcomm v (fsuc n) (inl (SequenceMap.map S.f (fst n) x)))
            (HL-normal n x)

        hatR-coh : (n : Fin 5) (x : fst Xs (fst n))
          → Square (cong (CW↪ Ct (suc (fst n))) (hatR (injectSuc n) x)) (hatR (fsuc n) (inl x))
            (fcomm w (fsuc n) (inl (SequenceMap.map S.g (fst n) x)))
            (cong (CW↪ Ct (suc (fst n))) (cong (SequenceMap.map T.g (suc (fst n)))
              (fcomm u (injectSuc n) x)))
        hatR-coh n x =
          cong-∙ (CW↪ Ct (suc (fst n)))
            (sym (fcomm w (injectSuc n) (SequenceMap.map S.g (fst n) x)))
            (fhom HR (injectSuc n) x)
          ◁ rebase-square
            (cong (CW↪ Ct (suc (fst n))) (fhom HR (injectSuc n) x))
            (fhom HR (fsuc n) (inl x))
            (cong (CW↪ Ct (suc (fst n))) (fcomm w (injectSuc n) (SequenceMap.map S.g (fst n) x)))
            (cong (CW↪ Ct (suc (fst n))) (cong (SequenceMap.map T.g (suc (fst n)))
              (fcomm u (injectSuc n) x)))
            (fcomm w (fsuc n) (inl (SequenceMap.map S.g (fst n) x)))
            (HR-normal n x)

        S_total : (n : Fin 5) (x : fst Xs (fst n))
          → Square
            (cong (CW↪ Yt (suc (fst n))) (stage-seam (injectSuc n) x))
            (stage-seam (fsuc n) (inl x))
            (cong (leftYt (suc (fst n))) (fcomm v (fsuc n) (inl (SequenceMap.map S.f (fst n) x))))
            (cong (rightYt (suc (fst n))) (fcomm w (fsuc n) (inl (SequenceMap.map S.g (fst n) x))))
        S_total n x =
          cong-∙∙ (CW↪ Yt (suc (fst n)))
            (cong (leftYt (fst n)) (hatL (injectSuc n) x))
            (push (fmap u (injectSuc (injectSuc n)) x))
            (sym (cong (rightYt (fst n)) (hatR (injectSuc n) x)))
          ◁ (λ j → cong (leftYt (suc (fst n))) (hatL-coh n x j)
            ∙∙ (λ i → push (fcomm u (injectSuc n) x j) i)
            ∙∙ sym (cong (rightYt (suc (fst n))) (hatR-coh n x j)))

        S_total-unfold : (n : Fin 5) (x : fst Xs (fst n))
          → Path (Square
            (cong (CW↪ Yt (suc (fst n))) (stage-seam (injectSuc n) x))
            (stage-seam (fsuc n) (inl x))
            (cong (leftYt (suc (fst n))) (fcomm v (fsuc n) (inl (SequenceMap.map S.f (fst n) x))))
            (cong (rightYt (suc (fst n))) (fcomm w (fsuc n) (inl (SequenceMap.map S.g (fst n) x)))))
            (S_total n x)
            (
          cong-∙∙ (CW↪ Yt (suc (fst n)))
            (cong (leftYt (fst n)) (hatL (injectSuc n) x))
            (push (fmap u (injectSuc (injectSuc n)) x))
            (sym (cong (rightYt (fst n)) (hatR (injectSuc n) x)))
          ◁ (λ j → cong (leftYt (suc (fst n))) (hatL-coh n x j)
            ∙∙ (λ i → push (fcomm u (injectSuc n) x j) i)
            ∙∙ sym (cong (rightYt (suc (fst n))) (hatR-coh n x j)))
            )
        S_total-unfold n x = refl

      total-comm : (n : Fin 6) (x : fst Ys (fst n))
        → CW↪ Yt (fst n) (total-stage (injectSuc n) x)
        ≡ total-stage (fsuc n) (CW↪ Ys (fst n) x)
      total-comm (zero , p) x = Empty.rec (CW₀-empty Ys x)
      total-comm (suc n , p) (inl y) = cong (leftYt (suc n)) (fcomm v (suc n , p) y)
      total-comm (suc n , p) (inr z) = cong (rightYt (suc n)) (fcomm w (suc n , p) z)
      total-comm (suc n , p) (push x i) j = S_total (n , p) x j i

    total-window : FiniteSpan6 → finCellMap 6 Ys Yt
    fmap (total-window d) = total-stage d
    fcomm (total-window d) = total-comm d
