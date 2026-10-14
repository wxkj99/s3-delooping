{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ContinuousBoundaryNatural where

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
import DeloopS3.Bridge.DegreeSpan.TopBoundaryNatural as Boundary
import DeloopS3.Bridge.DegreeSpan.FiniteSpanWitness as Witness

-- Generic continuous Lemma E for the fixed strict triangular LES packages.
-- This does not select a finite span outside propositional truncation, nor
-- does it specialize to the ShortCase cover-degree calculation.
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
      -- The literal packaged H₃ → H₂ boundaries, with no FiniteSpan6 premise.
      geometric-top-boundary-natural
        : compGroupHom
            (H̃ˢᵏᵉˡ→ {C = W.Ys} {D = W.Yt} 3 (W.P u∞ v∞ w∞ hL∞ hR∞))
            (SpanSequenceData.boundary (snd TargetLES.strict-pushoutLES) 2)
         ≡ compGroupHom
            (SpanSequenceData.boundary (snd SourceLES.strict-pushoutLES) 2)
            (H̃ˢᵏᵉˡ→ {C = W.Xs} {D = W.Xt} 2 u∞)
      geometric-top-boundary-natural =
        PT.rec
          (isSetGroupHom {G = H̃ˢᵏᵉˡ W.Ys 3} {H = H̃ˢᵏᵉˡ W.Xt 2} _ _)
          (B.geometric-top-boundary-natural u∞ v∞ w∞ hL∞ hR∞)
          (F.finite-span6-merely u∞ v∞ w∞ hL∞ hR∞)
