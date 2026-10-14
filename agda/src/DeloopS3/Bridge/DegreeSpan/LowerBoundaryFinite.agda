{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerBoundaryFinite where

-- H2 → H1 naturality for the literal specified strict triangular packages.
-- Geometry retains window6; homology beta uses total window5/overlap window4.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group using (GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom ; GroupHom≡)
open import Cubical.CW.Base using (CWskel ; realise ; realiseSeq)
open import Cubical.CW.Map using
  (cellMap ; realiseCellMap ; finCellMap ; finCellMap↓ ; finCellMap→FinSeqColim
  ; finCellMap→finChainComplexMap ; module prefunctoriality)
open import Cubical.CW.Approximation using (finCellApprox)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→ ; H̃ˢᵏᵉˡ→-pre ; H̃ˢᵏᵉˡ→β)
open import Cubical.CW.Strictification using (strictCWskel)
import Cubical.HITs.SequentialColimit as SC
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Bridge.DegreeSpan.LowerBoundaryCycles
import DeloopS3.Bridge.DegreeSpan.LowerCube as LowerCube
import DeloopS3.Bridge.DegreeSpan.LowerBoundaryDegree as LowerR
import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Strict as Packaging
open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)

module TotalWindowBoundary (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
  module S = SpecifiedBoundary Os Ls Rs fs gs
  module T = SpecifiedBoundary Ot Lt Rt ft gt
  module N = LowerR.TotalWindowNaturality Os Ls Rs Ot Lt Rt fs gs ft gt

  module SourceLES = Packaging.Strict Os Ls Rs fs gs
    (record { q-is-equiv = S.Q.q-is-equiv })
  module TargetLES = Packaging.Strict Ot Lt Rt ft gt
    (record { q-is-equiv = T.Q.q-is-equiv })

  module _
    (u∞ : realise W.Xs → realise W.Xt)
    (v∞ : realise W.Bs → realise W.Bt)
    (w∞ : realise W.Cs → realise W.Ct)
    (hL∞ : (x : realise W.Xs) → v∞ (W.fS∞ x) ≡ W.fT∞ (u∞ x))
    (hR∞ : (x : realise W.Xs) → w∞ (W.gS∞ x) ≡ W.gT∞ (u∞ x))
    (d : W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where

    private
      module Data = W.FiniteSpan6 {u∞ = u∞} {v∞ = v∞} {w∞ = w∞}
        {hL∞ = hL∞} {hR∞ = hR∞} d

    Φ₆ : finCellMap 6 W.Ys W.Yt
    Φ₆ = C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d
    Φ₅ : finCellMap 5 W.Ys W.Yt
    Φ₅ = finCellMap↓ Φ₆
    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = C.u₆ u∞ v∞ w∞ hL∞ hR∞ d
    u₄ : finCellMap 4 W.Xs W.Xt
    u₄ = finCellMap↓ (finCellMap↓ u₆)

    Φ-cycle : S.HY.Cycle → T.HY.Cycle
    Φ-cycle = finite-cycle (finCellMap→finChainComplexMap 3 Φ₅) (2 , tt)
    u-cycle : S.HX.Cycle → T.HX.Cycle
    u-cycle = finite-cycle (finCellMap→finChainComplexMap 2 u₄) (1 , tt)

    overlap-window4 : finCellApprox W.Xs W.Xt u∞ 4
    fst overlap-window4 = u₄
    snd overlap-window4 = SC.→FinSeqColimHomotopy
      (SC.FinSeqColim→Colim 4 ∘ finCellMap→FinSeqColim W.Xs W.Xt u₄)
      (u∞ ∘ SC.FinSeqColim→Colim 4)
      (λ x → funExt⁻ (snd Data.aO) (SC.fincl (4 , tt) x))

    -- Both shorter approximations retain the markings of the SAME window6.
    total-window5 : finCellApprox W.Ys W.Yt (W.P u∞ v∞ w∞ hL∞ hR∞) 5
    fst total-window5 = Φ₅
    snd total-window5 = SC.→FinSeqColimHomotopy
      (SC.FinSeqColim→Colim 5 ∘ finCellMap→FinSeqColim W.Ys W.Yt Φ₅)
      (W.P u∞ v∞ w∞ hL∞ hR∞ ∘ SC.FinSeqColim→Colim 5)
      (λ x → funExt⁻ (snd (fst (W.total-window-approx u∞ v∞ w∞ hL∞ hR∞ d)))
        (SC.fincl (5 , tt) x))

    abstract
      total-window-homology-β
        : H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞)
         ≡ H̃ˢᵏᵉˡ→-pre W.Ys W.Yt 2 Φ₅
      total-window-homology-β = H̃ˢᵏᵉˡ→β W.Ys W.Yt 2 total-window5

      overlap-window-homology-β
        : H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞
         ≡ H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 1 u₄
      overlap-window-homology-β = H̃ˢᵏᵉˡ→β W.Xs W.Xt 1 overlap-window4

      lower-boundary-cycle-natural : (z : S.HY.Cycle)
        → T.R-cycle (Φ-cycle z) ≡ u-cycle (S.R-cycle z)
      lower-boundary-cycle-natural z = T.HX.cycle-path
        (T.R-cycle-coefficient (Φ-cycle z)
        ∙ funExt⁻ (cong fst
            (N.lower-R-natural-unconditional u∞ v∞ w∞ hL∞ hR∞ d)) (fst z)
        ∙ cong (fst (prefunctoriality.chainFunct 6 u₆ (1 , tt)))
            (sym (S.R-cycle-coefficient z)))

      finite-lower-boundary-natural
        : compGroupHom (H̃ˢᵏᵉˡ→-pre W.Ys W.Yt 2 Φ₅) T.δ
         ≡ compGroupHom S.δ (H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 1 u₄)
      finite-lower-boundary-natural = GroupHom≡ (funExt
        (SQ.elimProp (λ _ → GroupStr.is-set (snd (H̃ˢᵏᵉˡ W.Xt 1)) _ _)
          (λ z → cong (fst T.δ)
              (finite-cycle-β (finCellMap→finChainComplexMap 3 Φ₅) (2 , tt) z)
            ∙ T.δ-cycle-β (Φ-cycle z)
            ∙ cong T.HX.class (lower-boundary-cycle-natural z)
            ∙ sym (finite-cycle-β (finCellMap→finChainComplexMap 2 u₄)
                (1 , tt) (S.R-cycle z))
            ∙ cong (fst (H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 1 u₄))
                (sym (S.δ-cycle-β z)))))

      lower-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞)) T.δ
         ≡ compGroupHom S.δ (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞)
      lower-boundary-natural =
        cong (λ h → compGroupHom h T.δ)
          total-window-homology-β
        ∙ finite-lower-boundary-natural
        ∙ cong (compGroupHom S.δ) (sym overlap-window-homology-β)

      lower-boundary-natural-inverse-comparison
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞)) T.δ-inverse
         ≡ compGroupHom S.δ-inverse (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞)
      lower-boundary-natural-inverse-comparison =
        cong (compGroupHom
          (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞)))
          T.δ-inverse-comparison-agrees
        ∙ lower-boundary-natural
        ∙ cong (λ h → compGroupHom h (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞))
            (sym S.δ-inverse-comparison-agrees)

      geometric-lower-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞))
            (SpanSequenceData.boundary (snd TargetLES.strict-pushoutLES) 1)
         ≡ compGroupHom
            (SpanSequenceData.boundary (snd SourceLES.strict-pushoutLES) 1)
            (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞)
      geometric-lower-boundary-natural =
        cong (compGroupHom
          (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞)))
          (TargetLES.strict-boundary-β 1)
        ∙ lower-boundary-natural-inverse-comparison
        ∙ cong (λ h → compGroupHom h (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞))
            (sym (SourceLES.strict-boundary-β 1))
