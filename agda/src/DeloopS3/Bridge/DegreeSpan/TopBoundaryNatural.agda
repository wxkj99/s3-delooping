{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopBoundaryNatural where

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
open import DeloopS3.Bridge.DegreeSpan.TopBoundaryCycles
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube
import DeloopS3.Bridge.DegreeSpan.TopCubeFinalDegree as Degree
import DeloopS3.Bridge.DegreeSpan.TopRNaturalUnconditional as TopR
import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Strict as Packaging
open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)

-- Lemma E on the specified skeletal presentations. The boundary is exactly
-- the triangular χ comparison followed by the DMC projection and
-- the fixed augmentation-presentation map (SpecifiedBoundary.δ).
-- No arbitrary ComparisonInput witnesses are identified here.
module TotalWindowBoundary (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
  module S = SpecifiedBoundary Os Ls Rs fs gs
  module T = SpecifiedBoundary Ot Lt Rt ft gt
  module N = TopR.TotalWindowNaturality Os Ls Rs Ot Lt Rt fs gs ft gt
  module D = Degree.TotalWindowDegree Os Ls Rs Ot Lt Rt fs gs ft gt

  -- These are the specified triangular packages, not arbitrary
  -- ComparisonInput witnesses. The q-is-equiv proofs are those used by
  -- Packaging.Unconditional.triangular-input and Approx.strict-span-comparison.
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
    u₆ : finCellMap 6 W.Xs W.Xt
    u₆ = C.u₆ u∞ v∞ w∞ hL∞ hR∞ d
    u₅ : finCellMap 5 W.Xs W.Xt
    u₅ = finCellMap↓ u₆

    Φ-cycle : S.HY.Cycle → T.HY.Cycle
    Φ-cycle = finite-cycle (finCellMap→finChainComplexMap 4 Φ₆) (3 , tt)
    u-cycle : S.HX.Cycle → T.HX.Cycle
    u-cycle = finite-cycle (finCellMap→finChainComplexMap 3 u₅) (2 , tt)

    -- Restrict the SAME chosen overlap approximation, not a new choice.
    overlap-window5 : finCellApprox W.Xs W.Xt u∞ 5
    fst overlap-window5 = u₅
    snd overlap-window5 = SC.→FinSeqColimHomotopy
      (SC.FinSeqColim→Colim 5 ∘ finCellMap→FinSeqColim W.Xs W.Xt u₅)
      (u∞ ∘ SC.FinSeqColim→Colim 5)
      (λ x → funExt⁻ (snd Data.aO) (SC.fincl (5 , tt) x))

    abstract
      overlap-window-homology-β
        : H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞
         ≡ H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 2 u₅
      overlap-window-homology-β = H̃ˢᵏᵉˡ→β W.Xs W.Xt 2 overlap-window5

      -- Coefficients of both target cycles agree by top-R naturality.
      top-boundary-cycle-natural : (z : S.HY.Cycle)
        → T.R-cycle (Φ-cycle z) ≡ u-cycle (S.R-cycle z)
      top-boundary-cycle-natural z = T.HX.cycle-path
        (T.R-cycle-coefficient (Φ-cycle z)
        ∙ funExt⁻ (cong fst
            (N.top-R-natural-unconditional u∞ v∞ w∞ hL∞ hR∞ d)) (fst z)
        ∙ cong (fst (prefunctoriality.chainFunct 6 u₆ (2 , tt)))
            (sym (S.R-cycle-coefficient z)))

      finite-top-boundary-natural
        : compGroupHom (H̃ˢᵏᵉˡ→-pre W.Ys W.Yt 3 Φ₆) T.δ
         ≡ compGroupHom S.δ (H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 2 u₅)
      finite-top-boundary-natural = GroupHom≡ (funExt
        (SQ.elimProp (λ _ → GroupStr.is-set (snd (H̃ˢᵏᵉˡ W.Xt 2)) _ _)
          (λ z → cong (fst T.δ)
              (finite-cycle-β (finCellMap→finChainComplexMap 4 Φ₆) (3 , tt) z)
            ∙ T.δ-cycle-β (Φ-cycle z)
            ∙ cong T.HX.class (top-boundary-cycle-natural z)
            ∙ sym (finite-cycle-β (finCellMap→finChainComplexMap 3 u₅)
                (2 , tt) (S.R-cycle z))
            ∙ cong (fst (H̃ˢᵏᵉˡ→-pre W.Xs W.Xt 2 u₅))
                (sym (S.δ-cycle-β z)))))

      -- Continuous total and overlap maps, with a specified FiniteSpan6 approximation.
      -- FiniteSpanWitness constructs this finite approximation under truncation.
      top-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞)) T.δ
         ≡ compGroupHom S.δ (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞)
      top-boundary-natural =
        cong (λ h → compGroupHom h T.δ)
          (D.total-window-homology-β u∞ v∞ w∞ hL∞ hR∞ d)
        ∙ finite-top-boundary-natural
        ∙ cong (compGroupHom S.δ) (sym overlap-window-homology-β)

      -- The boundary uses the literal inverse-q comparison from strict packaging.
      -- The theorem below exposes the corresponding geometric LES boundary field.
      top-boundary-natural-inverse-comparison
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞)) T.δ-inverse
         ≡ compGroupHom S.δ-inverse (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞)
      top-boundary-natural-inverse-comparison =
        cong (compGroupHom
          (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞)))
          T.δ-inverse-comparison-agrees
        ∙ top-boundary-natural
        ∙ cong (λ h → compGroupHom h (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞))
            (sym S.δ-inverse-comparison-agrees)

      -- Literal geometric LES boundary fields for the specified packages.
      -- Degree 3 is augmented index 4; the boundary field is indexed by 2.
      geometric-top-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞))
            (SpanSequenceData.boundary (snd TargetLES.strict-pushoutLES) 2)
         ≡ compGroupHom
            (SpanSequenceData.boundary (snd SourceLES.strict-pushoutLES) 2)
            (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞)
      geometric-top-boundary-natural =
        cong (compGroupHom
          (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞)))
          (TargetLES.strict-boundary-β 2)
        ∙ top-boundary-natural-inverse-comparison
        ∙ cong (λ h → compGroupHom h (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞))
            (sym (SourceLES.strict-boundary-β 2))
