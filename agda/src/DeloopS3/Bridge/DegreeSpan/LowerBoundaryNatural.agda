{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerBoundaryNatural where

-- Continuous H2 → H1 boundary naturality, with no finite-span or cube premise.
-- These are the specified strict triangular LES packages, not chosen witnesses.
-- Ordinary H2 has augmented coefficient index 3. Geometry stays at window6;
-- only the marked homology approximations are restricted to windows 5 and 4.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (snd)
open import Cubical.Algebra.Group.MorphismProperties
  using (compGroupHom ; isSetGroupHom)
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→)
open import Cubical.CW.Strictification using (strictCWskel)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)
import DeloopS3.Bridge.DegreeSpan.LowerBoundaryFinite as Boundary
import DeloopS3.Bridge.DegreeSpan.FiniteSpanWitness as Witness

module TotalWindowBoundary (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module B = Boundary.TotalWindowBoundary Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = B.W
  module SourceLES = B.SourceLES
  module TargetLES = B.TargetLES
  private
    module F = Witness.Window ℓ-zero Os Ls Rs Ot Lt Rt fs gs ft gt

  module _
    (u∞ : realise W.Xs → realise W.Xt)
    (v∞ : realise W.Bs → realise W.Bt)
    (w∞ : realise W.Cs → realise W.Ct)
    (hL∞ : (x : realise W.Xs) → v∞ (W.fS∞ x) ≡ W.fT∞ (u∞ x))
    (hR∞ : (x : realise W.Xs) → w∞ (W.gS∞ x) ≡ W.gT∞ (u∞ x)) where

    abstract
      geometric-top-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 2 (W.P u∞ v∞ w∞ hL∞ hR∞))
            (SpanSequenceData.boundary (snd TargetLES.strict-pushoutLES) 1)
         ≡ compGroupHom
            (SpanSequenceData.boundary (snd SourceLES.strict-pushoutLES) 1)
            (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 1 u∞)
      geometric-top-boundary-natural =
        PT.rec
          (isSetGroupHom {G = H̃ˢᵏᵉˡ W.Ys 2} {H = H̃ˢᵏᵉˡ W.Xt 1} _ _)
          (B.geometric-lower-boundary-natural u∞ v∞ w∞ hL∞ hR∞)
          (F.finite-span6-merely u∞ v∞ w∞ hL∞ hR∞)

-- Reuse one skeleton, one pair of legs, and ONE literal LES for endomorphisms.
-- No equality of unrelated LES witnesses is required or asserted.
module SameSpanBoundary (O L R : CWskel ℓ-zero)
  (f : cellMap (strictCWskel O) (strictCWskel L))
  (g : cellMap (strictCWskel O) (strictCWskel R)) where

  module B = TotalWindowBoundary O L R O L R f g f g
  module W = B.W
  module LES = B.SourceLES

  module _
    (u∞ : realise W.Xs → realise W.Xs)
    (v∞ : realise W.Bs → realise W.Bs)
    (w∞ : realise W.Cs → realise W.Cs)
    (hL∞ : (x : realise W.Xs) → v∞ (W.fS∞ x) ≡ W.fS∞ (u∞ x))
    (hR∞ : (x : realise W.Xs) → w∞ (W.gS∞ x) ≡ W.gS∞ (u∞ x)) where

    abstract
      geometric-self-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Ys} 2 (W.P u∞ v∞ w∞ hL∞ hR∞))
            (SpanSequenceData.boundary (snd LES.strict-pushoutLES) 1)
         ≡ compGroupHom
            (SpanSequenceData.boundary (snd LES.strict-pushoutLES) 1)
            (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xs} 1 u∞)
      geometric-self-boundary-natural =
        B.geometric-top-boundary-natural u∞ v∞ w∞ hL∞ hR∞
