{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TotalWindowApprox where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws using (cong-∙ ; cong-∙∙)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin.Base using (Fin ; injectSuc ; fsuc ; flast)
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
import Cubical.HITs.SequentialColimit as SC
import Cubical.HITs.Pushout as PO
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; finCellMap ; finCellMap→FinSeqColim)
open import Cubical.CW.Homotopy using (finCellHom)
open import Cubical.CW.Approximation using (finCellApprox)
open import Cubical.CW.Strictification using (strictCWskel)
import DeloopS3.Bridge.DegreeSpan.TotalWindowStage as Stage
open import DeloopS3.Bridge.DegreeSpan.TotalWindowRealizationSquare
  using (marked-leg-square ; nested-seam)

open FinSequenceMap
open finCellHom
open Stage public using (restrictCell)

module Window (ℓ : Level) (Os Ls Rs Ot Lt Rt : CWskel ℓ)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module W = Stage.Window ℓ Os Ls Rs Ot Lt Rt fs gs ft gt
  open W public

  fS∞ : realise Xs → realise Bs
  fS∞ = realiseCellMap {C = Xs} {D = Bs} S.f
  gS∞ : realise Xs → realise Cs
  gS∞ = realiseCellMap {C = Xs} {D = Cs} S.g
  fT∞ : realise Xt → realise Bt
  fT∞ = realiseCellMap {C = Xt} {D = Bt} T.f
  gT∞ : realise Xt → realise Ct
  gT∞ = realiseCellMap {C = Xt} {D = Ct} T.g

  TotS TotT : Type ℓ
  TotS = PO.Pushout fS∞ gS∞
  TotT = PO.Pushout fT∞ gT∞

  leftS : realise Bs → TotS
  leftS = PO.inl
  rightS : realise Cs → TotS
  rightS = PO.inr
  leftT : realise Bt → TotT
  leftT = PO.inl
  rightT : realise Ct → TotT
  rightT = PO.inr

  join-seam : (a b : TotT) (x : realise Xt)
    → a ≡ leftT (fT∞ x) → b ≡ rightT (gT∞ x) → a ≡ b
  join-seam a b x l r = l ∙∙ PO.push x ∙∙ sym r

  KS : (n : Fin 6) → fst Ys (suc (fst n)) → TotS
  KS n z = Iso.fun S.realisePushoutSkel (SC.incl {n = suc (fst n)} z)
  KT : (n : Fin 6) → fst Yt (suc (fst n)) → TotT
  KT n z = Iso.fun T.realisePushoutSkel (SC.incl {n = suc (fst n)} z)

  module _
    (u∞ : realise Xs → realise Xt)
    (v∞ : realise Bs → realise Bt)
    (w∞ : realise Cs → realise Ct)
    (hL∞ : (x : realise Xs) → v∞ (fS∞ x) ≡ fT∞ (u∞ x))
    (hR∞ : (x : realise Xs) → w∞ (gS∞ x) ≡ gT∞ (u∞ x)) where

    span-total : TotS → TotT
    span-total (PO.inl y) = leftT (v∞ y)
    span-total (PO.inr z) = rightT (w∞ z)
    span-total (PO.push x i) =
      (cong leftT (hL∞ x) ∙∙ PO.push (u∞ x) ∙∙ sym (cong rightT (hR∞ x))) i

    P : realise Ys → realise Yt
    P = Iso.inv T.realisePushoutSkel ∘ span-total ∘ Iso.fun S.realisePushoutSkel

    module _ (d : FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where
      private
        module D = W.FiniteSpan6 {u∞ = u∞} {v∞ = v∞} {w∞ = w∞}
          {hL∞ = hL∞} {hR∞ = hR∞} d
        u₆ : finCellMap 6 Xs Xt
        u₆ = fst D.aO
        v₆ : finCellMap 6 Bs Bt
        v₆ = fst D.aL
        w₆ : finCellMap 6 Cs Ct
        w₆ = fst D.aR

        fsₙ : (n : Fin 6) → fst Xs (fst n) → fst Bs (fst n)
        fsₙ n = SequenceMap.map S.f (fst n)
        gsₙ : (n : Fin 6) → fst Xs (fst n) → fst Cs (fst n)
        gsₙ n = SequenceMap.map S.g (fst n)
        ftₙ : (n : Fin 6) → fst Xt (fst n) → fst Bt (fst n)
        ftₙ n = SequenceMap.map T.f (fst n)
        gtₙ : (n : Fin 6) → fst Xt (fst n) → fst Ct (fst n)
        gtₙ n = SequenceMap.map T.g (fst n)

        inclBt : (n : ℕ) → fst Bt n → realise Bt
        inclBt n = SC.incl {n = n}
        inclCt : (n : ℕ) → fst Ct n → realise Ct
        inclCt n = SC.incl {n = n}

        hatL′ : (n : Fin 6) (x : fst Xs (fst n))
          → fmap v₆ (fsuc n) (PO.inl (fsₙ n x))
          ≡ PO.inl (ftₙ n (fmap u₆ (injectSuc n) x))
        hatL′ = W.hatL u∞ v∞ w∞ hL∞ hR∞ d
        hatR′ : (n : Fin 6) (x : fst Xs (fst n))
          → fmap w₆ (fsuc n) (PO.inl (gsₙ n x))
          ≡ PO.inl (gtₙ n (fmap u₆ (injectSuc n) x))
        hatR′ = W.hatR u∞ v∞ w∞ hL∞ hR∞ d

        seam : (n : Fin 6) (x : fst Xs (fst n))
          → Path (fst Yt (suc (fst n)))
            (PO.inl (fmap v₆ (fsuc n) (PO.inl (fsₙ n x))))
            (PO.inr (fmap w₆ (fsuc n) (PO.inl (gsₙ n x))))
        seam = W.stage-seam u∞ v∞ w∞ hL∞ hR∞ d
        stage′ : (n : Fin 6) → fst Ys (suc (fst n)) → fst Yt (suc (fst n))
        stage′ = W.stage u∞ v∞ w∞ hL∞ hR∞ d

      alphaO0 : (n : Fin 6) (x : fst Xs (fst n))
        → SC.incl (fmap u₆ (injectSuc n) x) ≡ u∞ (SC.incl x)
      alphaO0 n x = funExt⁻ (snd D.aO) (SC.fincl (injectSuc n) x)
      alphaL0 : (n : Fin 6) (y : fst Bs (fst n))
        → SC.incl (fmap v₆ (injectSuc n) y) ≡ v∞ (SC.incl y)
      alphaL0 n y = funExt⁻ (snd D.aL) (SC.fincl (injectSuc n) y)
      alphaL1 : (n : Fin 6) (y : fst Bs (suc (fst n)))
        → SC.incl (fmap v₆ (fsuc n) y) ≡ v∞ (SC.incl y)
      alphaL1 n y = funExt⁻ (snd D.aL) (SC.fincl (fsuc n) y)
      alphaR0 : (n : Fin 6) (y : fst Cs (fst n))
        → SC.incl (fmap w₆ (injectSuc n) y) ≡ w∞ (SC.incl y)
      alphaR0 n y = funExt⁻ (snd D.aR) (SC.fincl (injectSuc n) y)
      alphaR1 : (n : Fin 6) (y : fst Cs (suc (fst n)))
        → SC.incl (fmap w₆ (fsuc n) y) ≡ w∞ (SC.incl y)
      alphaR1 n y = funExt⁻ (snd D.aR) (SC.fincl (fsuc n) y)

      abstract
        appL : (n : Fin 6) (x : fst Xs (fst n))
          → Square
            (SC.push (fmap v₆ (injectSuc n) (fsₙ n x))
              ∙ cong (inclBt (suc (fst n))) (fcomm v₆ n (fsₙ n x)))
            (cong v∞ (SC.push (fsₙ n x)))
            (alphaL0 n (fsₙ n x)) (alphaL1 n (PO.inl (fsₙ n x)))
        appL n x =
          sym (cong-∙ (SC.FinSeqColim→Colim 6 {X = realiseSeq Bt})
            (SC.fpush n (fmap v₆ (injectSuc n) (fsₙ n x)))
            (cong (SC.fincl (fsuc n)) (fcomm v₆ n (fsₙ n x))))
          ◁ (λ j i → snd D.aL j (SC.fpush n (fsₙ n x) i))

        appR : (n : Fin 6) (x : fst Xs (fst n))
          → Square
            (SC.push (fmap w₆ (injectSuc n) (gsₙ n x))
              ∙ cong (inclCt (suc (fst n))) (fcomm w₆ n (gsₙ n x)))
            (cong w∞ (SC.push (gsₙ n x)))
            (alphaR0 n (gsₙ n x)) (alphaR1 n (PO.inl (gsₙ n x)))
        appR n x =
          sym (cong-∙ (SC.FinSeqColim→Colim 6 {X = realiseSeq Ct})
            (SC.fpush n (fmap w₆ (injectSuc n) (gsₙ n x)))
            (cong (SC.fincl (fsuc n)) (fcomm w₆ n (gsₙ n x))))
          ◁ (λ j i → snd D.aR j (SC.fpush n (gsₙ n x) i))

      Lcell : (n : Fin 6) (x : fst Xs (fst n))
        → SC.incl (fmap v₆ (fsuc n) (PO.inl (fsₙ n x)))
        ≡ fT∞ (SC.incl (fmap u₆ (injectSuc n) x))
      Lcell n x = cong (inclBt (suc (fst n))) (hatL′ n x)
        ∙ sym (SC.push (ftₙ n (fmap u₆ (injectSuc n) x)))
      Rcell : (n : Fin 6) (x : fst Xs (fst n))
        → SC.incl (fmap w₆ (fsuc n) (PO.inl (gsₙ n x)))
        ≡ gT∞ (SC.incl (fmap u₆ (injectSuc n) x))
      Rcell n x = cong (inclCt (suc (fst n))) (hatR′ n x)
        ∙ sym (SC.push (gtₙ n (fmap u₆ (injectSuc n) x)))
      Lcont : (n : Fin 6) (x : fst Xs (fst n))
        → v∞ (SC.incl (PO.inl (fsₙ n x))) ≡ fT∞ (u∞ (SC.incl x))
      Lcont n x = sym (cong v∞ (SC.push (fsₙ n x))) ∙ hL∞ (SC.incl x)
      Rcont : (n : Fin 6) (x : fst Xs (fst n))
        → w∞ (SC.incl (PO.inl (gsₙ n x))) ≡ gT∞ (u∞ (SC.incl x))
      Rcont n x = sym (cong w∞ (SC.push (gsₙ n x))) ∙ hR∞ (SC.incl x)

      abstract
        legL : (n : Fin 6) (x : fst Xs (fst n))
          → Square (Lcell n x) (Lcont n x)
            (alphaL1 n (PO.inl (fsₙ n x))) (cong fT∞ (alphaO0 n x))
        legL n x =
          cong (_∙ sym (SC.push (ftₙ n (fmap u₆ (injectSuc n) x))))
            (cong-∙ (inclBt (suc (fst n)))
              (sym (fcomm v₆ n (fsₙ n x))) (fhom (fst D.H_L) n x))
          ◁ marked-leg-square
            (SC.push (fmap v₆ (injectSuc n) (fsₙ n x)))
            (cong (inclBt (suc (fst n))) (fcomm v₆ n (fsₙ n x)))
            (SC.push (ftₙ n (fmap u₆ (injectSuc n) x)))
            (cong (inclBt (suc (fst n))) (fhom (fst D.H_L) n x))
            (alphaL0 n (fsₙ n x)) (alphaL1 n (PO.inl (fsₙ n x)))
            (cong v∞ (SC.push (fsₙ n x)))
            (hL∞ (SC.incl x)) (cong fT∞ (alphaO0 n x))
            (snd D.H_L n x) (appL n x)

        legR : (n : Fin 6) (x : fst Xs (fst n))
          → Square (Rcell n x) (Rcont n x)
            (alphaR1 n (PO.inl (gsₙ n x))) (cong gT∞ (alphaO0 n x))
        legR n x =
          cong (_∙ sym (SC.push (gtₙ n (fmap u₆ (injectSuc n) x))))
            (cong-∙ (inclCt (suc (fst n)))
              (sym (fcomm w₆ n (gsₙ n x))) (fhom (fst D.H_R) n x))
          ◁ marked-leg-square
            (SC.push (fmap w₆ (injectSuc n) (gsₙ n x)))
            (cong (inclCt (suc (fst n))) (fcomm w₆ n (gsₙ n x)))
            (SC.push (gtₙ n (fmap u₆ (injectSuc n) x)))
            (cong (inclCt (suc (fst n))) (fhom (fst D.H_R) n x))
            (alphaR0 n (gsₙ n x)) (alphaR1 n (PO.inl (gsₙ n x)))
            (cong w∞ (SC.push (gsₙ n x)))
            (hR∞ (SC.incl x)) (cong gT∞ (alphaO0 n x))
            (snd D.H_R n x) (appR n x)

      cell-seam : (n : Fin 6) (x : fst Xs (fst n))
        → Path TotT
          (leftT (SC.incl (fmap v₆ (fsuc n) (PO.inl (fsₙ n x)))))
          (rightT (SC.incl (fmap w₆ (fsuc n) (PO.inl (gsₙ n x)))))
      cell-seam n x = cong leftT (Lcell n x)
        ∙∙ PO.push (SC.incl (fmap u₆ (injectSuc n) x)) ∙∙ sym (cong rightT (Rcell n x))
      cont-seam : (n : Fin 6) (x : fst Xs (fst n))
        → Path TotT
          (leftT (v∞ (SC.incl (PO.inl (fsₙ n x)))))
          (rightT (w∞ (SC.incl (PO.inl (gsₙ n x)))))
      cont-seam n x = cong leftT (Lcont n x)
        ∙∙ PO.push (u∞ (SC.incl x)) ∙∙ sym (cong rightT (Rcont n x))

      abstract
        target-normal : (n : Fin 6) (x : fst Xs (fst n))
          → cong (KT n) (seam n x) ≡ cell-seam n x
        target-normal n x =
          cong-∙∙ (KT n) (cong (leftYt (fst n)) (hatL′ n x))
            (PO.push (fmap u₆ (injectSuc n) x))
            (sym (cong (rightYt (fst n)) (hatR′ n x)))
          ∙ nested-seam
            (cong leftT (cong (inclBt (suc (fst n))) (hatL′ n x)))
            (cong leftT (sym (SC.push (ftₙ n (fmap u₆ (injectSuc n) x)))))
            (PO.push (SC.incl (fmap u₆ (injectSuc n) x)))
            (cong rightT (cong (inclCt (suc (fst n))) (hatR′ n x)))
            (cong rightT (sym (SC.push (gtₙ n (fmap u₆ (injectSuc n) x)))))
          ∙ cong₂ (join-seam
              (leftT (SC.incl (fmap v₆ (fsuc n) (PO.inl (fsₙ n x)))))
              (rightT (SC.incl (fmap w₆ (fsuc n) (PO.inl (gsₙ n x)))))
              (SC.incl (fmap u₆ (injectSuc n) x)))
            (sym (cong-∙ leftT (cong (inclBt (suc (fst n))) (hatL′ n x))
              (sym (SC.push (ftₙ n (fmap u₆ (injectSuc n) x))))))
            (sym (cong-∙ rightT (cong (inclCt (suc (fst n))) (hatR′ n x))
              (sym (SC.push (gtₙ n (fmap u₆ (injectSuc n) x))))))

        source-normal : (n : Fin 6) (x : fst Xs (fst n))
          → cong (span-total ∘ KS n) (PO.push x) ≡ cont-seam n x
        source-normal n x =
          cong-∙∙ span-total
            (cong leftS (sym (SC.push (fsₙ n x))))
            (PO.push (SC.incl x))
            (cong rightS (SC.push (gsₙ n x)))
          ∙ nested-seam
            (cong leftT (sym (cong v∞ (SC.push (fsₙ n x)))))
            (cong leftT (hL∞ (SC.incl x)))
            (PO.push (u∞ (SC.incl x)))
            (cong rightT (sym (cong w∞ (SC.push (gsₙ n x)))))
            (cong rightT (hR∞ (SC.incl x)))
          ∙ cong₂ (join-seam
              (leftT (v∞ (SC.incl (PO.inl (fsₙ n x)))))
              (rightT (w∞ (SC.incl (PO.inl (gsₙ n x)))))
              (u∞ (SC.incl x)))
            (sym (cong-∙ leftT (sym (cong v∞ (SC.push (fsₙ n x)))) (hL∞ (SC.incl x))))
            (sym (cong-∙ rightT (sym (cong w∞ (SC.push (gsₙ n x)))) (hR∞ (SC.incl x))))

        normalized-square : (n : Fin 6) (x : fst Xs (fst n))
          → Square (cell-seam n x) (cont-seam n x)
            (cong leftT (alphaL1 n (PO.inl (fsₙ n x))))
            (cong rightT (alphaR1 n (PO.inl (gsₙ n x))))
        normalized-square n x j = cong leftT (legL n x j)
          ∙∙ (λ i → PO.push (alphaO0 n x j) i) ∙∙ sym (cong rightT (legR n x j))

        actual-square : (n : Fin 6) (x : fst Xs (fst n))
          → Square (cong (KT n) (seam n x)) (cong (span-total ∘ KS n) (PO.push x))
            (cong leftT (alphaL1 n (PO.inl (fsₙ n x))))
            (cong rightT (alphaR1 n (PO.inl (gsₙ n x))))
        actual-square n x = target-normal n x ◁ (normalized-square n x ▷ sym (source-normal n x))

      stage-over : (n : Fin 6) (z : fst Ys (suc (fst n)))
        → KT n (stage′ n z) ≡ span-total (KS n z)
      stage-over n (PO.inl y) = cong leftT (alphaL1 n y)
      stage-over n (PO.inr z) = cong rightT (alphaR1 n z)
      stage-over n (PO.push x i) j = actual-square n x j i

      top-over : (z : fst Ys 6)
        → SC.incl {n = 6} (fmap (total-window u∞ v∞ w∞ hL∞ hR∞ d) flast z)
        ≡ P (SC.incl {n = 6} z)
      top-over z = sym (Iso.ret T.realisePushoutSkel (SC.incl {n = 6} (stage′ flast z)))
        ∙ cong (Iso.inv T.realisePushoutSkel) (stage-over flast z)

    total-window-approx : (d : FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞)
      → Σ[ a ∈ finCellApprox Ys Yt P 6 ] fst a ≡ total-window u∞ v∞ w∞ hL∞ hR∞ d
    total-window-approx d =
      ((total-window u∞ v∞ w∞ hL∞ hR∞ d , SC.→FinSeqColimHomotopy
        (SC.FinSeqColim→Colim 6 ∘ finCellMap→FinSeqColim Ys Yt (total-window u∞ v∞ w∞ hL∞ hR∞ d))
        (P ∘ SC.FinSeqColim→Colim 6) (top-over d)) , refl)
