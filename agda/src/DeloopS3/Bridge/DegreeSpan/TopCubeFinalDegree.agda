{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopCubeFinalDegree where

-- Finite coefficient naturality follows from a quotient-level square.
-- The homology β theorem uses a finite approximation without extending it
-- to a global cellMap or identifying its cellular coefficients.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.HITs.Susp using
  (Susp ; north ; south ; merid ; suspFun ; congSuspIso)
open import Cubical.HITs.SphereBouquet using
  (SphereBouquet ; BouquetIso-gen ; sphereBouquetSuspIso ; bouquetSusp→)
open import Cubical.HITs.SphereBouquet.Degree using
  (bouquetDegree ; bouquetDegreeComp ; bouquetDegreeSusp)
open import Cubical.Algebra.AbGroup using (AbGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using (CWskel ; cofibCW ; realise)
open import Cubical.CW.Map using
  (cellMap ; finCellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.CW.Homotopy using (cofibIso)
open import Cubical.CW.Homology.Base using
  (H̃ˢᵏᵉˡ→ ; H̃ˢᵏᵉˡ→-pre ; H̃ˢᵏᵉˡ→β)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.Cellular using (Z)
import DeloopS3.Bridge.DegreeSpan.TopCube as TopCube

private
  BQ : (T : CWskel ℓ-zero) (n : ℕ)
    → Iso (cofibCW n T) (SphereBouquet n (Fin (snd T .fst n)))
  BQ T n = BouquetIso-gen n (snd T .fst n)
    (snd T .snd .fst n) (snd T .snd .snd .snd n)

  abstract
    suspIso-suspFun-local : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
      (e₁ : Iso A B) (e₂ : Iso C D) (f : C → A)
      → Iso.fun (congSuspIso e₁) ∘ suspFun f ∘ Iso.inv (congSuspIso e₂)
       ≡ suspFun (Iso.fun e₁ ∘ f ∘ Iso.inv e₂)
    suspIso-suspFun-local e₁ e₂ f i north = north
    suspIso-suspFun-local e₁ e₂ f i south = south
    suspIso-suspFun-local e₁ e₂ f i (merid a j) =
      merid ((Iso.fun e₁ ∘ f ∘ Iso.inv e₂) a) j

    cofibIso-suspFun-local : (n : ℕ) (S T : CWskel ℓ-zero)
      (f : cofibCW n S → cofibCW n T)
      → Iso.fun (cofibIso n T) ∘ suspFun f ∘ Iso.inv (cofibIso n S)
       ≡ bouquetSusp→ (Iso.fun (BQ T n) ∘ f ∘ Iso.inv (BQ S n))
    cofibIso-suspFun-local n S T f =
      cong (λ k → Iso.fun sphereBouquetSuspIso ∘ k
        ∘ Iso.inv sphereBouquetSuspIso)
        (suspIso-suspFun-local (BQ T n) (BQ S n) f)

module FiniteRetractionDegree (Xs Xt Ys Yt : CWskel ℓ-zero)
  (U : finCellMap 6 Xs Xt) (F : finCellMap 6 Ys Yt)
  (rs : cofibCW 3 Ys → Susp (cofibCW 2 Xs))
  (rt : cofibCW 3 Yt → Susp (cofibCW 2 Xt)) where

  QΦ : cofibCW 3 Ys → cofibCW 3 Yt
  QΦ = prefunctoriality.fn+1/fn 6 F (3 , tt)

  Qu : cofibCW 2 Xs → cofibCW 2 Xt
  Qu = prefunctoriality.fn+1/fn 6 U (2 , tt)

  private
    φbar : SphereBouquet 3 (Fin (snd Ys .fst 3))
      → SphereBouquet 3 (Fin (snd Yt .fst 3))
    φbar = Iso.fun (BQ Yt 3) ∘ QΦ ∘ Iso.inv (BQ Ys 3)

    ubar : SphereBouquet 2 (Fin (snd Xs .fst 2))
      → SphereBouquet 2 (Fin (snd Xt .fst 2))
    ubar = Iso.fun (BQ Xt 2) ∘ Qu ∘ Iso.inv (BQ Xs 2)

    rsbar : SphereBouquet 3 (Fin (snd Ys .fst 3))
      → SphereBouquet 3 (Fin (snd Xs .fst 2))
    rsbar = Iso.fun (cofibIso 2 Xs) ∘ rs ∘ Iso.inv (BQ Ys 3)

    rtbar : SphereBouquet 3 (Fin (snd Yt .fst 3))
      → SphereBouquet 3 (Fin (snd Xt .fst 2))
    rtbar = Iso.fun (cofibIso 2 Xt) ∘ rt ∘ Iso.inv (BQ Yt 3)

    Ubar : SphereBouquet 3 (Fin (snd Xs .fst 2))
      → SphereBouquet 3 (Fin (snd Xt .fst 2))
    Ubar = Iso.fun (cofibIso 2 Xt) ∘ suspFun Qu
      ∘ Iso.inv (cofibIso 2 Xs)

  Rs : AbGroupHom (Z Ys 3) (Z Xs 2)
  Rs = bouquetDegree rsbar

  Rt : AbGroupHom (Z Yt 3) (Z Xt 2)
  Rt = bouquetDegree rtbar

  private
    abstract
      suspended-quotient-degree : bouquetDegree Ubar
        ≡ prefunctoriality.chainFunct 6 U (2 , tt)
      suspended-quotient-degree =
        cong bouquetDegree (cofibIso-suspFun-local 2 Xs Xt Qu)
        ∙ sym (bouquetDegreeSusp ubar)

  abstract
    retraction-degree-natural : rt ∘ QΦ ≡ suspFun Qu ∘ rs
      → compGroupHom (prefunctoriality.chainFunct 6 F (3 , tt)) Rt
       ≡ compGroupHom Rs (prefunctoriality.chainFunct 6 U (2 , tt))
    retraction-degree-natural natural =
      sym (bouquetDegreeComp rtbar φbar)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso 2 Xt) ∘ rt)
            (Iso.ret (BQ Yt 3) (QΦ (Iso.inv (BQ Ys 3) z))))
      ∙ cong bouquetDegree
          (cong (λ k → Iso.fun (cofibIso 2 Xt) ∘ k ∘ Iso.inv (BQ Ys 3))
            natural)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso 2 Xt) ∘ suspFun Qu)
            (sym (Iso.ret (cofibIso 2 Xs) (rs (Iso.inv (BQ Ys 3) z)))))
      ∙ bouquetDegreeComp Ubar rsbar
      ∙ cong (compGroupHom Rs) suspended-quotient-degree

module TotalWindowDegree (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = TopCube.TopCube Os Ls Rs Ot Lt Rt fs gs ft gt

  module _
    (u∞ : realise C.W.Xs → realise C.W.Xt)
    (v∞ : realise C.W.Bs → realise C.W.Bt)
    (w∞ : realise C.W.Cs → realise C.W.Ct)
    (hL∞ : (x : realise C.W.Xs)
      → v∞ (realiseCellMap {C = C.W.Xs} {D = C.W.Bs} C.W.S.f x)
      ≡ realiseCellMap {C = C.W.Xt} {D = C.W.Bt} C.W.T.f (u∞ x))
    (hR∞ : (x : realise C.W.Xs)
      → w∞ (realiseCellMap {C = C.W.Xs} {D = C.W.Cs} C.W.S.g x)
      ≡ realiseCellMap {C = C.W.Xt} {D = C.W.Ct} C.W.T.g (u∞ x))
    (d : C.W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where

    private
      module D = FiniteRetractionDegree C.W.Xs C.W.Xt C.W.Ys C.W.Yt
        (C.u₆ u∞ v∞ w∞ hL∞ hR∞ d)
        (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d)
        (C.S.prismRet 2) (C.T.prismRet 2)

    abstract
      -- The specified seam cube supplies the quotient-level naturality square.
      finite-top-R-natural-from-seam
        : C.RemainingSeamCube u∞ v∞ w∞ hL∞ hR∞ d
        → compGroupHom
            (prefunctoriality.chainFunct 6
              (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d) (3 , tt)) (C.T.R 2)
         ≡ compGroupHom (C.S.R 2)
            (prefunctoriality.chainFunct 6
              (C.u₆ u∞ v∞ w∞ hL∞ hR∞ d) (2 , tt))
      finite-top-R-natural-from-seam K = D.retraction-degree-natural
        (C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d K)

      -- Homology β needs the approximation, not a seam-cube witness.
      -- It identifies homology maps only, not cellular coefficients.
      total-window-homology-β
        : H̃ˢᵏᵉˡ→ {C = C.W.Ys} {D = C.W.Yt} 3
            (C.W.P u∞ v∞ w∞ hL∞ hR∞)
         ≡ H̃ˢᵏᵉˡ→-pre C.W.Ys C.W.Yt 3
            (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d)
      total-window-homology-β =
        H̃ˢᵏᵉˡ→β C.W.Ys C.W.Yt 3
          {f = C.W.P u∞ v∞ w∞ hL∞ hR∞}
          (fst (C.W.total-window-approx u∞ v∞ w∞ hL∞ hR∞ d))
        ∙ cong (H̃ˢᵏᵉˡ→-pre C.W.Ys C.W.Yt 3)
            (snd (C.W.total-window-approx u∞ v∞ w∞ hL∞ hR∞ d))
