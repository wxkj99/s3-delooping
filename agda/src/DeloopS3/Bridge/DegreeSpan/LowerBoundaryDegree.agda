{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.LowerBoundaryDegree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc)
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
open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_ ; <ᵗ-trans ; <ᵗsuc)
import DeloopS3.Bridge.DegreeSpan.LowerCube as LowerCube
import DeloopS3.Bridge.DegreeSpan.LowerCubeAssemble as Assembly

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

module FiniteRetractionDegree (m n : ℕ) (p : suc n <ᵗ m)
  (Xs Xt Ys Yt : CWskel ℓ-zero)
  (U : finCellMap m Xs Xt) (F : finCellMap m Ys Yt)
  (rs : cofibCW (suc n) Ys → Susp (cofibCW n Xs))
  (rt : cofibCW (suc n) Yt → Susp (cofibCW n Xt)) where

  QΦ : cofibCW (suc n) Ys → cofibCW (suc n) Yt
  QΦ = prefunctoriality.fn+1/fn m F ((suc n) , p)

  Qu : cofibCW n Xs → cofibCW n Xt
  Qu = prefunctoriality.fn+1/fn m U (n , <ᵗ-trans <ᵗsuc p)

  private
    φbar : SphereBouquet (suc n) (Fin (snd Ys .fst (suc n)))
      → SphereBouquet (suc n) (Fin (snd Yt .fst (suc n)))
    φbar = Iso.fun (BQ Yt (suc n)) ∘ QΦ ∘ Iso.inv (BQ Ys (suc n))

    ubar : SphereBouquet n (Fin (snd Xs .fst n))
      → SphereBouquet n (Fin (snd Xt .fst n))
    ubar = Iso.fun (BQ Xt n) ∘ Qu ∘ Iso.inv (BQ Xs n)

    rsbar : SphereBouquet (suc n) (Fin (snd Ys .fst (suc n)))
      → SphereBouquet (suc n) (Fin (snd Xs .fst n))
    rsbar = Iso.fun (cofibIso n Xs) ∘ rs ∘ Iso.inv (BQ Ys (suc n))

    rtbar : SphereBouquet (suc n) (Fin (snd Yt .fst (suc n)))
      → SphereBouquet (suc n) (Fin (snd Xt .fst n))
    rtbar = Iso.fun (cofibIso n Xt) ∘ rt ∘ Iso.inv (BQ Yt (suc n))

    Ubar : SphereBouquet (suc n) (Fin (snd Xs .fst n))
      → SphereBouquet (suc n) (Fin (snd Xt .fst n))
    Ubar = Iso.fun (cofibIso n Xt) ∘ suspFun Qu
      ∘ Iso.inv (cofibIso n Xs)

  Rs : AbGroupHom (Z Ys (suc n)) (Z Xs n)
  Rs = bouquetDegree rsbar

  Rt : AbGroupHom (Z Yt (suc n)) (Z Xt n)
  Rt = bouquetDegree rtbar

  private
    abstract
      suspended-quotient-degree : bouquetDegree Ubar
        ≡ prefunctoriality.chainFunct m U (n , <ᵗ-trans <ᵗsuc p)
      suspended-quotient-degree =
        cong bouquetDegree (cofibIso-suspFun-local n Xs Xt Qu)
        ∙ sym (bouquetDegreeSusp ubar)

  abstract
    retraction-degree-natural : rt ∘ QΦ ≡ suspFun Qu ∘ rs
      → compGroupHom (prefunctoriality.chainFunct m F ((suc n) , p)) Rt
       ≡ compGroupHom Rs (prefunctoriality.chainFunct m U (n , <ᵗ-trans <ᵗsuc p))
    retraction-degree-natural natural =
      sym (bouquetDegreeComp rtbar φbar)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso n Xt) ∘ rt)
            (Iso.ret (BQ Yt (suc n)) (QΦ (Iso.inv (BQ Ys (suc n)) z))))
      ∙ cong bouquetDegree
          (cong (λ k → Iso.fun (cofibIso n Xt) ∘ k ∘ Iso.inv (BQ Ys (suc n)))
            natural)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso n Xt) ∘ suspFun Qu)
            (sym (Iso.ret (cofibIso n Xs) (rs (Iso.inv (BQ Ys (suc n)) z)))))
      ∙ bouquetDegreeComp Ubar rsbar
      ∙ cong (compGroupHom Rs) suspended-quotient-degree

-- This coefficient bridge is generic in degree n and finite window m.
-- Its lower-boundary instance below fixes n = 1 and retains window 6.
module TotalWindowNaturality (Os Ls Rs Ot Lt Rt : CWskel ℓ-zero)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module C = LowerCube.LowerCube Os Ls Rs Ot Lt Rt fs gs ft gt
  module W = C.W
  module S = C.S
  module T = C.T
  module A = Assembly.Assemble Os Ls Rs Ot Lt Rt fs gs ft gt

  module _
    (u∞ : realise W.Xs → realise W.Xt)
    (v∞ : realise W.Bs → realise W.Bt)
    (w∞ : realise W.Cs → realise W.Ct)
    (hL∞ : (x : realise W.Xs) → v∞ (W.fS∞ x) ≡ W.fT∞ (u∞ x))
    (hR∞ : (x : realise W.Xs) → w∞ (W.gS∞ x) ≡ W.gT∞ (u∞ x))
    (d : W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞) where

    private
      module D = FiniteRetractionDegree 6 1 tt W.Xs W.Xt W.Ys W.Yt
        (C.u₆ u∞ v∞ w∞ hL∞ hR∞ d)
        (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d)
        (S.prismRet 1) (T.prismRet 1)

    abstract
      prismRet-natural-unconditional
        : T.prismRet 1 ∘ C.Q₂Φ u∞ v∞ w∞ hL∞ hR∞ d
         ≡ suspFun (C.Q₁u u∞ v∞ w∞ hL∞ hR∞ d) ∘ S.prismRet 1
      prismRet-natural-unconditional =
        C.prismRet-natural-from-seam u∞ v∞ w∞ hL∞ hR∞ d
          (A.direct-seam-residual u∞ v∞ w∞ hL∞ hR∞ d)

      lower-R-natural-unconditional
        : compGroupHom
            (prefunctoriality.chainFunct 6
              (C.Φ₆ u∞ v∞ w∞ hL∞ hR∞ d) (2 , tt)) (T.R 1)
         ≡ compGroupHom (S.R 1)
            (prefunctoriality.chainFunct 6
              (C.u₆ u∞ v∞ w∞ hL∞ hR∞ d) (1 , tt))
      lower-R-natural-unconditional =
        D.retraction-degree-natural prismRet-natural-unconditional
