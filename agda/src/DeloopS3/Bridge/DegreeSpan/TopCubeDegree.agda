{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeDegree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Susp using (Susp ; suspFun)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using (CWskel ; cofibCW)
open import Cubical.CW.Map using (cellMap ; finCellMap ; module prefunctoriality)
open import DeloopS3.Bridge.CellularPushout.Cellular using
  (restrictCell ; cellular-coefficients ; cellular-cofib-window)
import DeloopS3.Bridge.DegreeSpan.TopRetractionDegree as Degree

-- Transfer finite naturality to the global degree theorem using exact
-- restriction identifications, without identifying the finite and global homotopies.
module FiniteRetractionDegree (Xs Xt Ys Yt : CWskel ℓ-zero)
  (u : cellMap Xs Xt) (Φ : cellMap Ys Yt)
  (rs : cofibCW 3 Ys → Susp (cofibCW 2 Xs))
  (rt : cofibCW 3 Yt → Susp (cofibCW 2 Xt)) where

  module D = Degree.RetractionDegree Xs Xt Ys Yt u Φ rs rt

  finite-natural : (U : finCellMap 6 Xs Xt) (F : finCellMap 6 Ys Yt)
    → Type
  finite-natural U F = Path (cofibCW 3 Ys → Susp (cofibCW 2 Xt))
    (rt ∘ prefunctoriality.fn+1/fn 6 F (3 , tt))
    (suspFun (prefunctoriality.fn+1/fn 6 U (2 , tt)) ∘ rs)

  abstract
    restriction-natural : (U : finCellMap 6 Xs Xt)
      (F : finCellMap 6 Ys Yt)
      → restrictCell u 6 ≡ U → restrictCell Φ 6 ≡ F
      → finite-natural U F
      → rt ∘ Degree.Q Φ 3 ≡ suspFun (Degree.Q u 2) ∘ rs
    restriction-natural U F ue fe h =
      sym (cong (λ q → rt ∘ q) (cellular-cofib-window Φ 5 3 tt))
      ∙ subst2 finite-natural (sym ue) (sym fe) h
      ∙ cong (λ q → suspFun q ∘ rs) (cellular-cofib-window u 5 2 tt)

    finite-degree-natural : (U : finCellMap 6 Xs Xt)
      (F : finCellMap 6 Ys Yt)
      → restrictCell u 6 ≡ U → restrictCell Φ 6 ≡ F
      → finite-natural U F
      → compGroupHom (cellular-coefficients Φ 3) D.Rt
       ≡ compGroupHom D.Rs (cellular-coefficients u 2)
    finite-degree-natural U F ue fe h =
      D.retraction-degree-natural (restriction-natural U F ue fe h)
