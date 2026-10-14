{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerBoundaryDescent where

-- Choose ONE strict LES before quantifying over continuous self-span maps.
-- Transport the entire package (LES plus universal H2 -> H1 naturality),
-- so both occurrences of every leg and CW presentation change together.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using
  (CWskel ; finCWskel ; finCWskel→CWskel ; realise ; isCW ; isFinCW)
open import Cubical.CW.Map using (cellMap ; realiseCellMap)
open import Cubical.CW.Strictification using (strictCWskel ; strictCwMap≡)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr ; push)
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; H̃ᶜʷ→ ; Finite≤ ; finite≤→isFinCW)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (GeometricPushoutLES ; SpanSequenceData)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology
  using (realisedCW)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Descent
  using (realised-CW-path)
import DeloopS3.Bridge.CellularPushout.PrismChains.Approx.Geometry as Geometry
import DeloopS3.Bridge.DegreeSpan.LowerBoundaryNatural as Lower
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Cert.Interpret.Realization as R

cw-span : (O L V : CW₀) → (fst O → fst L) → (fst O → fst V)
  → R.Span ℓ-zero ℓ-zero ℓ-zero
R.Span.O (cw-span O L V f g) = fst O
R.Span.L (cw-span O L V f g) = fst L
R.Span.R (cw-span O L V f g) = fst V
R.Span.left (cw-span O L V f g) = f
R.Span.right (cw-span O L V f g) = g

module _ (O L V : CW₀) (f : fst O → fst L) (g : fst O → fst V) where

  SelfSpanMap : Type₀
  SelfSpanMap = Map.ContinuousSpanMap (cw-span O L V f g) (cw-span O L V f g)

  SameSpanBoundary : (w : isCW (Pushout f g)) → Type₁
  SameSpanBoundary w =
    Σ[ les ∈ GeometricPushoutLES O L V f g (Pushout f g , w) ]
      ((m : SelfSpanMap) →
        compGroupHom
          (H̃ᶜʷ→ {C = Pushout f g , w} {D = Pushout f g , w} 2 (Map.totalMap m))
          (SpanSequenceData.boundary (snd les) 1)
        ≡ compGroupHom
          (SpanSequenceData.boundary (snd les) 1)
          (H̃ᶜʷ→ {C = O} {D = O} 1 (Map.overlapMap m)))

  -- The truncation encloses the single choice AND all self-span maps,
  -- including their two specified attachment homotopies.
  AllSelfMaps : Type₁
  AllSelfMaps = (w : isCW (Pushout f g)) → PT.∥ SameSpanBoundary w ∥₁

AllLegs : (O L V : CW₀) → Type₁
AllLegs O L V = (f : fst O → fst L) (g : fst O → fst V)
  → AllSelfMaps O L V f g

module Strict (O L V : CWskel ℓ-zero)
  (f : cellMap (strictCWskel O) (strictCWskel L))
  (g : cellMap (strictCWskel O) (strictCWskel V)) where

  module N = Lower.SameSpanBoundary O L V f g
  module W = N.W

  StrictMap : Type₀
  StrictMap = SelfSpanMap
    (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs) W.fS∞ W.gS∞

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

    normalized : AllSelfMaps
      (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs) W.fS∞ W.gS∞
    normalized w = PT.∣ subst
      (SameSpanBoundary
        (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs) W.fS∞ W.gS∞)
      (PT.squash₁ PT.∣ W.S.hasCWskelPushout ∣₁ w)
      (N.LES.strict-pushoutLES , λ m →
        cong (λ p → compGroupHom
          (H̃ᶜʷ→ {C = N.LES.Pᶜʷ} {D = N.LES.Pᶜʷ} 2 p)
          (SpanSequenceData.boundary (snd N.LES.strict-pushoutLES) 1))
          (sym (total-agrees m))
        ∙ N.geometric-self-boundary-natural
          (Map.overlapMap m) (Map.leftMap m) (Map.rightMap m)
          (Map.leftSquare m) (Map.rightSquare m)) ∣₁

    cellular : AllSelfMaps
      (realisedCW (strictCWskel O)) (realisedCW (strictCWskel L))
      (realisedCW (strictCWskel V)) (realiseCellMap f) (realiseCellMap g)
    cellular = subst2
      (λ h k → AllSelfMaps
        (realisedCW W.Xs) (realisedCW W.Bs) (realisedCW W.Cs)
        (realiseCellMap h) (realiseCellMap k))
      (strictCwMap≡ f) (strictCwMap≡ g) normalized

-- Approximate the two legs ONCE, before introducing any self-span map.
-- Only the overlap needs a finite skeleton for these two choices.
module Finite (n : ℕ) (O : finCWskel ℓ-zero n) (L V : CWskel ℓ-zero) where

  O′ = finCWskel→CWskel n O
  Oᶜʷ = realisedCW (strictCWskel O′)
  Lᶜʷ = realisedCW (strictCWskel L)
  Vᶜʷ = realisedCW (strictCWskel V)

  abstract
    all-legs : AllLegs Oᶜʷ Lᶜʷ Vᶜʷ
    all-legs f g w = PT.rec2 PT.squash₁
      (λ (h , hp) (k , kp) →
        subst2 (λ u v → AllSelfMaps Oᶜʷ Lᶜʷ Vᶜʷ u v)
          hp kp (Strict.cellular O′ L V h k) w)
      (Geometry.finite-strict-approximation n O L f)
      (Geometry.finite-strict-approximation n O V g)

abstract
  -- Each of the three variables occurs simultaneously in source and target.
  -- The entire one-LES-plus-universal-equation package is transported.
  descend-presentations : (O L V : CW₀) (SO SL SV : CWskel ℓ-zero)
    (eo : fst O ≃ realise SO) (el : fst L ≃ realise SL)
    (ev : fst V ≃ realise SV)
    → AllLegs (realisedCW SO) (realisedCW SL) (realisedCW SV)
    → AllLegs O L V
  descend-presentations O L V SO SL SV eo el ev =
    transport (λ i → AllLegs
      (realised-CW-path O SO eo i) (realised-CW-path L SL el i)
      (realised-CW-path V SV ev i))

  -- Public generic theorem: one LES, universally natural for all actual
  -- continuous self-span maps, all inside ONE propositional truncation.
  finite-same-span-boundary-natural : (O L V : CW₀)
    → isFinCW (fst O) → isFinCW (fst L) → isFinCW (fst V)
    → (f : fst O → fst L) (g : fst O → fst V) (w : isCW (Pushout f g))
    → PT.∥ Σ[ les ∈ GeometricPushoutLES O L V f g (Pushout f g , w) ]
        ((m : Map.ContinuousSpanMap (cw-span O L V f g) (cw-span O L V f g)) →
          compGroupHom
            (H̃ᶜʷ→ {C = Pushout f g , w} {D = Pushout f g , w} 2 (Map.totalMap m))
            (SpanSequenceData.boundary (snd les) 1)
          ≡ compGroupHom
            (SpanSequenceData.boundary (snd les) 1)
            (H̃ᶜʷ→ {C = O} {D = O} 1 (Map.overlapMap m))) ∥₁
  finite-same-span-boundary-natural O L V finO finL finV f g w =
    PT.rec3 PT.squash₁
      (λ (no , SO , eo) (nl , SL , el) (nv , SV , ev) →
        descend-presentations O L V
          (strictCWskel (finCWskel→CWskel no SO))
          (strictCWskel (finCWskel→CWskel nl SL))
          (strictCWskel (finCWskel→CWskel nv SV))
          (compEquiv eo (Geometry.strict-realisation-equiv (finCWskel→CWskel no SO)))
          (compEquiv el (Geometry.strict-realisation-equiv (finCWskel→CWskel nl SL)))
          (compEquiv ev (Geometry.strict-realisation-equiv (finCWskel→CWskel nv SV)))
          (Finite.all-legs no SO (finCWskel→CWskel nl SL) (finCWskel→CWskel nv SV))
          f g w)
      finO finL finV

  -- Dimension-bounded convenience interface; the resulting package is
  -- exactly the same one, with no matrix or finite-span premise.
  finite≤-same-span-boundary-natural : (O L V : CW₀) (dO dL dV : ℕ)
    → Finite≤ dO (fst O) → Finite≤ dL (fst L) → Finite≤ dV (fst V)
    → (f : fst O → fst L) (g : fst O → fst V) (w : isCW (Pushout f g))
    → PT.∥ SameSpanBoundary O L V f g w ∥₁
  finite≤-same-span-boundary-natural O L V dO dL dV finO finL finV =
    finite-same-span-boundary-natural O L V
      (finite≤→isFinCW finO) (finite≤→isFinCW finL) (finite≤→isFinCW finV)
