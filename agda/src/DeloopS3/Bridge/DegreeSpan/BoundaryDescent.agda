{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.BoundaryDescent where

-- Transport a jointly chosen pair of LESs and its actual-map equation.
-- Component maps AND their specified homotopies stay universally quantified
-- while the four legs and then the six presentations are substituted.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using
  (CWskel ; finCWskel ; finCWskel→CWskel ; realise ; isCW)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Strictification using (strictCWskel ; strictCwMap≡)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr ; push)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (GeometricPushoutLES ; SpanSequenceData)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
  using (realisedCW)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Descent
  using (realised-CW-path)
import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Geometry as Geometry
import DeloopS3.Bridge.DegreeSpan.ContinuousBoundaryNatural as Continuous
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Cert.Interpret.Realization as R

cw-span : (O L V : CW₀) → (fst O → fst L) → (fst O → fst V)
  → R.Span ℓ-zero ℓ-zero ℓ-zero
R.Span.O (cw-span O L V f g) = fst O
R.Span.L (cw-span O L V f g) = fst L
R.Span.R (cw-span O L V f g) = fst V
R.Span.left (cw-span O L V f g) = f
R.Span.right (cw-span O L V f g) = g

module _ (Os Ls Rs Ot Lt Rt : CW₀)
  (fs : fst Os → fst Ls) (gs : fst Os → fst Rs)
  (ft : fst Ot → fst Lt) (gt : fst Ot → fst Rt) where

  PairedBoundary : (ws : isCW (Pushout fs gs)) (wt : isCW (Pushout ft gt))
    → (Pushout fs gs → Pushout ft gt) → (fst Os → fst Ot) → Type₁
  PairedBoundary ws wt p u =
    Σ[ sourceLES ∈ GeometricPushoutLES Os Ls Rs fs gs (Pushout fs gs , ws) ]
    Σ[ targetLES ∈ GeometricPushoutLES Ot Lt Rt ft gt (Pushout ft gt , wt) ]
      compGroupHom
        (H̃ᶜʷ→ {C = Pushout fs gs , ws} {D = Pushout ft gt , wt} 3 p)
        (SpanSequenceData.boundary (snd targetLES) 2)
      ≡ compGroupHom
        (SpanSequenceData.boundary (snd sourceLES) 2)
        (H̃ᶜʷ→ {C = Os} {D = Ot} 2 u)

  -- The quantification over m includes leftSquare and rightSquare. Thus
  -- dependent substitution preserves Map.totalMap with its actual seams.
  AllSpanMaps : Type₁
  AllSpanMaps = (m : Map.ContinuousSpanMap
      (cw-span Os Ls Rs fs gs) (cw-span Ot Lt Rt ft gt))
    (ws : isCW (Pushout fs gs)) (wt : isCW (Pushout ft gt))
    → PT.∥ PairedBoundary ws wt (Map.totalMap m) (Map.overlapMap m) ∥₁

AllLegs : (Os Ls Rs Ot Lt Rt : CW₀) → Type₁
AllLegs Os Ls Rs Ot Lt Rt =
  (fs : fst Os → fst Ls) (gs : fst Os → fst Rs)
  (ft : fst Ot → fst Lt) (gt : fst Ot → fst Rt)
  → AllSpanMaps Os Ls Rs Ot Lt Rt fs gs ft gt

module Strict (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module N = Continuous.TotalWindowBoundary Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = N.W

  StrictMap : Type₀
  StrictMap = Map.ContinuousSpanMap
    (cw-span (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs) W.fS∞ W.gS∞)
    (cw-span (realisedCW W.Xt) (realisedCW W.Bt) (realisedCW W.Ct) W.fT∞ W.gT∞)

  abstract
    total-agrees : (m : StrictMap)
      → W.span-total (Map.overlapMap m) (Map.leftMap m) (Map.rightMap m)
          (Map.leftSquare m) (Map.rightSquare m) ≡ Map.totalMap m
    total-agrees m = funExt pointwise
      where
      pointwise : (x : W.TotS)
        → W.span-total (Map.overlapMap m) (Map.leftMap m) (Map.rightMap m)
            (Map.leftSquare m) (Map.rightSquare m) x ≡ Map.totalMap m x
      pointwise (inl x) = refl
      pointwise (inr x) = refl
      pointwise (push x i) = refl

    normalized : AllSpanMaps
      (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs)
      (realisedCW W.Xt) (realisedCW W.Bt) (realisedCW W.Ct)
      W.fS∞ W.gS∞ W.fT∞ W.gT∞
    normalized m ws wt = PT.∣ subst2
      (λ a b → PairedBoundary
        (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs)
        (realisedCW W.Xt) (realisedCW W.Bt) (realisedCW W.Ct)
        W.fS∞ W.gS∞ W.fT∞ W.gT∞ a b
        (Map.totalMap m) (Map.overlapMap m))
      (PT.squash₁ PT.∣ W.S.hasCWskelPushout ∣₁ ws)
      (PT.squash₁ PT.∣ W.T.hasCWskelPushout ∣₁ wt)
      (N.SourceLES.strict-pushoutLES , N.TargetLES.strict-pushoutLES ,
        (cong (λ p → compGroupHom
          (H̃ᶜʷ→ {C = N.SourceLES.Pᶜʷ} {D = N.TargetLES.Pᶜʷ} 3 p)
          (SpanSequenceData.boundary (snd N.TargetLES.strict-pushoutLES) 2))
          (sym (total-agrees m))
        ∙ N.geometric-top-boundary-natural
          (Map.overlapMap m) (Map.leftMap m) (Map.rightMap m)
          (Map.leftSquare m) (Map.rightSquare m))) ∣₁

    cellular : AllSpanMaps
      (realisedCW (strictCWskel Os)) (realisedCW (strictCWskel Ls))
      (realisedCW (strictCWskel Rs)) (realisedCW (strictCWskel Ot))
      (realisedCW (strictCWskel Lt)) (realisedCW (strictCWskel Rt))
      (realiseCellMap fs) (realiseCellMap gs)
      (realiseCellMap ft) (realiseCellMap gt)
    cellular = subst2
      (λ f g → AllSpanMaps
        (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs)
        (realisedCW W.Xt) (realisedCW W.Bt) (realisedCW W.Ct)
        (realiseCellMap f) (realiseCellMap g)
        (realiseCellMap ft) (realiseCellMap gt))
      (strictCwMap≡ fs) (strictCwMap≡ gs)
      (subst2
        (λ f g → AllSpanMaps
          (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs)
          (realisedCW W.Xt) (realisedCW W.Bt) (realisedCW W.Ct)
          W.fS∞ W.gS∞ (realiseCellMap f) (realiseCellMap g))
        (strictCwMap≡ ft) (strictCwMap≡ gt) normalized)

-- Four finite choices are eliminated only into the single truncated pair.
-- Finiteness of the two overlaps suffices for approximating all four legs.
module Finite (ms mt : ℕ)
  (Os : finCWskel ℓ-zero ms) (Ls Rs : CWskel ℓ-zero)
  (Ot : finCWskel ℓ-zero mt) (Lt Rt : CWskel ℓ-zero) where

  Os′ = finCWskel→CWskel ms Os
  Ot′ = finCWskel→CWskel mt Ot
  Oₛ = realisedCW (strictCWskel Os′)
  Lₛ = realisedCW (strictCWskel Ls)
  Rₛ = realisedCW (strictCWskel Rs)
  Oₜ = realisedCW (strictCWskel Ot′)
  Lₜ = realisedCW (strictCWskel Lt)
  Rₜ = realisedCW (strictCWskel Rt)

  abstract
    all-legs : AllLegs Oₛ Lₛ Rₛ Oₜ Lₜ Rₜ
    all-legs fs gs ft gt m ws wt = PT.rec2 PT.squash₁
      (λ (f , fp) (g , gp) → PT.rec2 PT.squash₁
        (λ (h , hp) (k , kp) →
          subst2 (λ u v → AllSpanMaps Oₛ Lₛ Rₛ Oₜ Lₜ Rₜ u v ft gt)
            fp gp
            (subst2 (λ u v → AllSpanMaps Oₛ Lₛ Rₛ Oₜ Lₜ Rₜ
                (realiseCellMap f) (realiseCellMap g) u v)
              hp kp (Strict.cellular Os′ Ls Rs Ot′ Lt Rt f g h k))
            m ws wt)
        (Geometry.finite-strict-approximation mt Ot Lt ft)
        (Geometry.finite-strict-approximation mt Ot Rt gt))
      (Geometry.finite-strict-approximation ms Os Ls fs)
      (Geometry.finite-strict-approximation ms Os Rs gs)

abstract
  -- No bespoke rechart cube: m, including BOTH specified squares, is a
  -- dependent argument of AllLegs. The conclusion retains Map.totalMap m.
  descend-presentations : (Os Ls Rs Ot Lt Rt : CW₀)
    (SO SL SR TO TL TR : CWskel ℓ-zero)
    (eo : fst Os ≃ realise SO) (el : fst Ls ≃ realise SL)
    (er : fst Rs ≃ realise SR) (fo : fst Ot ≃ realise TO)
    (fl : fst Lt ≃ realise TL) (fr : fst Rt ≃ realise TR)
    → AllLegs (realisedCW SO) (realisedCW SL) (realisedCW SR)
        (realisedCW TO) (realisedCW TL) (realisedCW TR)
    → AllLegs Os Ls Rs Ot Lt Rt
  descend-presentations Os Ls Rs Ot Lt Rt SO SL SR TO TL TR eo el er fo fl fr =
    transport (λ i → AllLegs
      (realised-CW-path Os SO eo i) (realised-CW-path Ls SL el i)
      (realised-CW-path Rs SR er i) (realised-CW-path Ot TO fo i)
      (realised-CW-path Lt TL fl i) (realised-CW-path Rt TR fr i))
